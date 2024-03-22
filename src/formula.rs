use crate::cli::{
    AddConsistency, ConEncoding, Experiment, IntEncoding, PbEncoding, SolveRecord, StaticsRecord,
};
use crate::cli::{EncodeRecord, System};
use crate::slurm::cmd;
use crate::{check_enc_timer, write_stats};
use std::fmt::{self, Display};
use std::io::Write;
use std::path::PathBuf;

use itertools::{Itertools, Position};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

use std::fs::remove_file;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::process::{Command, Stdio};

use crate::{rand_id, PbcEncoder};

use pindakaas::{
    Assignment, CheckError, ClauseDatabase, Cnf, Comparator, Encoder, IntLinExp, IntVarId,
    IntVarRef, Lin, LinearConstraint, LinearEncoder, Model, Obj, Result, Term, Unsatisfiable, Wcnf,
};

use std::collections::{HashMap, HashSet};
use std::time::Instant;

pub type Lit = i32;
pub type C = i64;

pub struct Formula {
    pub(crate) model: Model<Lit, C>,
    pub(crate) pb_model: Option<(Model<Lit, C>, HashMap<IntVarId, Vec<IntVarRef<Lit, C>>>)>,
    pub(crate) principal: Option<Lit>,
    pub(crate) wcnf: Wcnf<Lit, C>,
    // solver: *mut c_void,
    pub pbs: Vec<LinearConstraint<Lit, C>>,
    pub(crate) solver_timeout: Option<f32>,
    pub(crate) enc_timeout: Option<f32>,
    labels: HashMap<Lit, String>,
}

impl Formula {
    pub fn new(
        model: Model<Lit, C>,
        solver_timeout: Option<f32>,
        enc_timeout: Option<f32>,
    ) -> Self {
        Self {
            model,
            wcnf: Wcnf::<Lit, C>::default(),
            pb_model: None,
            principal: None,
            // solver: unsafe { ipasir_init() },
            pbs: vec![],
            solver_timeout,
            enc_timeout,
            labels: HashMap::new(),
        }
    }

    pub fn to_xcsp(&self, path: &Path) -> Result<(), std::io::Error> {
        let mut output = File::create(path)?;
        writeln!(output, "<instance>")?;
        writeln!(output, "<variables>")?;

        self.model.vars().iter().try_for_each(|x| {
            let x = x.borrow();
            writeln!(
                output,
                "<var id=\"x{}\"> {}..{} </var>",
                x.id,
                x.lb(),
                x.ub()
            )
        })?;

        writeln!(output, "</variables>")?;
        writeln!(output, "<constraints>")?;

        for (_, il) in self.model.constraints().enumerate() {
            writeln!(output, "<sum>")?;
            write!(output, "<list> ")?;
            for term in &il.exp.terms {
                write!(output, "x{} ", term.x.borrow().id)?;
            }
            writeln!(output, "</list>")?;

            write!(output, "<coeffs> ")?;
            for term in &il.exp.terms {
                write!(output, "{} ", term.c)?;
            }
            writeln!(output, "</coeffs>")?;
            writeln!(
                output,
                "<condition>({},{})</condition>",
                match il.cmp {
                    Comparator::LessEq => "le",
                    Comparator::Equal => "eq",
                    Comparator::GreaterEq => "ge",
                },
                il.k
            )?;
            writeln!(output, "</sum>")?;
        }

        writeln!(output, "</constraints>")?;
        writeln!(output, "</instance>")?;

        Ok(())
    }

    pub fn to_opb(&self, path: PathBuf, rewrite_leqs: bool) -> Result<(), std::io::Error> {
        println!("Write OPB {path:?}");

        let mut output = File::create(path)?;

        //let pbs = self.pbs.iter().map(|pb| pb.into::<())
        let vars = self
            .pbs
            .iter()
            .flat_map(|pb| pb.exp.terms())
            .map(|v| v.0)
            .collect::<HashSet<Lit>>()
            .len();

        writeln!(
            output,
            "* #variable= {} #constraint= {}",
            vars,
            self.pbs.len()
        )?;

        writeln!(output, ";",)?;

        for pb in &self.pbs {
            let pb = if pb.cmp == Comparator::LessEq && rewrite_leqs {
                let mut pb = pb.clone();
                pb.exp *= -1;
                pb.k = -pb.k;
                pb.cmp = Comparator::GreaterEq;
                pb
            } else {
                pb.clone()
            };
            for (lit, coef) in pb.exp.terms() {
                write!(
                    output,
                    //"{} {} x{} ",
                    "{:+} x{} ",
                    pb.exp.mult * coef,
                    //if coef.is_positive() { "+" } else { "-" },
                    //coef.abs(),
                    lit,
                )?;
            }
            writeln!(
                output,
                "{} {};",
                match pb.cmp {
                    pindakaas::Comparator::LessEq => "<=",
                    pindakaas::Comparator::Equal => "=",
                    pindakaas::Comparator::GreaterEq => ">=",
                },
                pb.k - pb.exp.add,
            )?;
        }
        Ok(())
    }

    pub fn stats(&self) -> StaticsRecord {
        StaticsRecord::new(
            self.wcnf.variables(),
            self.wcnf.clauses(),
            self.wcnf.literals(),
        )
    }

    pub fn assign(&self, lit_assignment: &[Lit]) -> Result<Assignment<C>, CheckError<Lit>> {
        if let Some((pb_model, pb_vars)) = self.pb_model.as_ref() {
            let pb_var_assignment = pb_model.assign(lit_assignment)?;
            Ok(Assignment(
                pb_vars
                    .iter()
                    .map(|(int_var_id, pb_vars)| {
                        (
                            int_var_id.clone(),
                            pb_vars
                                .iter()
                                .map(|pb_var| pb_var_assignment[&pb_var.borrow().id])
                                .sum(),
                        )
                    })
                    .collect(),
            ))
        } else {
            self.model.assign(&lit_assignment)
        }
    }

    pub fn assign_lits(&self, model: &[Lit]) -> HashMap<Lit, bool> {
        HashMap::from_iter(model.iter().map(|x| (x.abs(), x.is_positive())))
    }

    pub fn enumerate(
        &mut self,
        max: Option<usize>,
        sat_cmd: String,
        aux_out: Option<PathBuf>,
    ) -> Vec<Vec<Lit>> {
        let mut solutions = vec![];

        let mut i = 0;
        let principals = 1..=self.principal.unwrap();
        while let SolveRecord {
            solution: Some(solution),
            ..
        } = self.solve(
            sat_cmd.clone(),
            &Obj::Satisfy,
            42,
            principals.clone().max(),
            aux_out.clone(),
            None,
            false,
        ) {
            assert!(
                solution
                    .iter()
                    .enumerate()
                    .all(|(i, lit)| i + 1 == lit.unsigned_abs() as usize),
                "Weird model returned: {solution:?}"
            );
            if max.is_some() && i > max.unwrap() {
                println!("Max nbr {max:?} of solutions reached");
                break;
            } else {
                i += 1
            }
            let nogood = solution
                .iter()
                .map(|i| -*i)
                .filter(|x| principals.contains(&x.abs()))
                .collect::<Vec<Lit>>();
            self.add_clause(&nogood).unwrap();
            if let Some(aux_out) = &aux_out {
                let mut dimacs = aux_out.clone();
                dimacs.set_extension("dimacs");
                let dimacs = dimacs.as_path();
                let mut cnf = Cnf::<Lit>::from_file(dimacs).unwrap();
                cnf.add_clause(&nogood).unwrap();
                cnf.to_file(dimacs, None).unwrap();
            }

            solutions.push(solution);
        }

        solutions
    }

    pub fn add_weighted_clause(&mut self, cl: &[Lit], weight: C) -> Result {
        self.wcnf.add_weighted_clause(cl, Some(weight))
    }

    pub fn solver_name(sat_cmd: &Path) -> &str {
        sat_cmd.file_name().unwrap().to_str().unwrap()
    }

    pub fn solve_cmd(
        path: PathBuf,
        sat_cmd: PathBuf,
        solver_timeout: Option<f32>,
        solve_seed: usize,
        last_var: Lit,
        obj: &Obj<Lit, C>,
    ) -> SolveRecord {
        let solver_name = Self::solver_name(&sat_cmd);
        assert!(sat_cmd.exists());
        assert!(path.exists(), "DIMACS does not exist at: {path:?}");
        assert!([
            "kissat",
            "cadical",
            "open-wbo",
            "open-wbo-inc",
            "glucose_static",
            "glucose-simp"
        ]
        .contains(&solver_name));
        let mut cost: Option<C> = None;
        let mut status: Option<Status> = None;
        let mut solution: Vec<Lit> = vec![];
        let solve_timer = Instant::now();

        let mut args = vec![];
        args.push(format!("{}", path.display()));

        if let Some(time) = solver_timeout {
            match solver_name {
                "kissat" => {
                    assert!(obj.is_satisfy());
                    args.push(format!("--seed={solve_seed}"));
                    args.push(format!("--time={}", time));
                    status = Some(Status::Unknown); // kissat doesn't s-line on timeout
                }
                "cadical" => {
                    assert!(obj.is_satisfy());
                    args.push(format!("--seed={solve_seed}"));
                    args.push(String::from("-t"));
                    args.push(format!("{}", solver_timeout.unwrap()));
                }
                "open-wbo" => {
                    assert!(obj.is_satisfy());
                    let algorithm = 1;
                    args.push(format!("-algorithm={}", algorithm));
                    args.push(format!("-cpu-lim={}", time));
                    args.push(format!("-rnd-seed={solve_seed}"));
                }
                "glucose_static" | "glucose-simp" => {
                    assert!(obj.is_satisfy());
                    // args.push(format!("-algorithm={}", algorithm));
                    args.push(format!("-cpu-lim={}", time));
                    args.push(format!("-rnd-seed={solve_seed}"));
                    args.push(String::from("-model"));
                    // let verb = 1;
                    // args.push(format!("-verb={}", verb));
                }
                "open-wbo-inc" => {
                    assert!(!obj.is_satisfy());
                    args.push(format!("-rnd-seed={solve_seed}"));
                }
                slv => unreachable!("Unverified solver: {}", slv),
            };
        }

        println!("Running SAT cmd: {} {}", &sat_cmd.display(), args.join(" "));

        let output = Command::new(sat_cmd).args(args).output().unwrap();

        if output.status.code().unwrap_or(-1) == -1 {
            let out = String::from_utf8(output.stdout).unwrap();
            let err = String::from_utf8(output.stderr).unwrap();
            panic!("{}\n{}\n", out, err);
        }

        for line in String::from_utf8(output.stdout.clone()).unwrap().lines() {
            let mut tokens = line.split_whitespace();
            match tokens.next() {
                None | Some("c") => {
                    if let Some("UNKNOWN") = tokens.next() {
                        status = Some(Status::Unknown)
                    } else {
                        continue;
                    }
                }
                Some("o") => cost = Some(tokens.next().unwrap().parse().unwrap()),
                Some("s") => match tokens.next() {
                    Some("OPTIMUM") => status = Some(Status::Opt),
                    Some("SATISFIABLE") => status = Some(Status::Sat),
                    Some("UNSATISFIABLE") => status = Some(Status::Unsat),
                    Some("UNKNOWN") | Some("INDETERMINATE") => status = Some(Status::Unknown),
                    status => panic!("Unknown status: {status:?}"),
                },
                Some("v") => {
                    tokens
                        .flat_map(|t| t.parse::<Lit>())
                        .filter(|t| {
                            let var = t.abs();
                            0 < var && t.abs() <= last_var
                        })
                        .for_each(|lit| {
                            solution.push(lit);
                        });
                }
                line => panic!("Unexpected slv output: {:?}", line),
            }
        }
        let solve_time = solve_timer.elapsed().as_secs_f32();
        let status = status.unwrap_or_else(|| {
            panic!(
                "No status set in SAT output:
                {}
                \n
                {}
                ",
                String::from_utf8(output.stdout).unwrap(),
                std::fs::read_to_string(path).unwrap()
            )
        });
        let solution = matches!(status, Status::Sat | Status::Opt).then(|| solution);

        SolveRecord {
            status,
            solution,
            time: solve_time,
            cost,
            ..SolveRecord::default()
        }
    }

    pub fn write(&self, aux_out: Option<PathBuf>, obj: &Obj<Lit, C>) -> PathBuf {
        let mut path = aux_out.unwrap_or({
            #[cfg(not(debug_assertions))]
            let id = rand_id();
            #[cfg(debug_assertions)]
            let id = String::from("dev");
            let path = format!("/tmp/{id}.dimacs");
            std::path::PathBuf::from_str(&path).unwrap()
        });

        if path.is_dir() {
            path.push(format!("{}.dimacs", rand_id()))
        }

        print!("Writing SAT to file {} .. ", path.display());
        if obj.is_satisfy() {
            Cnf::from(self.wcnf.clone())
                .to_file(Path::new(&path), None)
                .unwrap();
        } else {
            self.wcnf.to_file(Path::new(&path), None).unwrap();
        };
        println!("done!");
        path
    }

    pub fn pbify(&mut self) {
        let mut pb_model = Model::<Lit, C>::new(0, &self.model.config);
        let pb_vars = self
            .model
            .vars()
            .iter()
            .map(|x| {
                let x = x.borrow();
                assert!(x.lb() == 0);
                let pb_enc = x
                    .dom
                    .iter()
                    .skip(1)
                    .map(|d| {
                        pb_model
                            .var(&[0, 1], Some(format!("{}>={d}", x.lbl())))
                            .unwrap()
                    })
                    .collect_vec();
                pb_enc
                    .iter()
                    .tuple_windows()
                    .try_for_each(|(a, b)| {
                        pb_model.add_constraint(Lin {
                            exp: IntLinExp {
                                terms: vec![Term::new(1, b.clone()), Term::new(-1, a.clone())],
                            },
                            cmp: Comparator::LessEq,
                            k: 0,
                            lbl: Some(format!("{} -> {}", b.borrow().lbl(), a.borrow().lbl())),
                        })
                    })
                    .unwrap();
                (x.id, pb_enc)
            })
            .collect::<HashMap<_, _>>();

        self.model
            .cons
            .iter()
            .cloned()
            .try_for_each(|con| {
                pb_model.add_constraint(Lin {
                    exp: IntLinExp {
                        terms: con
                            .exp
                            .terms
                            .into_iter()
                            .flat_map(|term| {
                                pb_vars[&term.x.borrow().id]
                                    .iter()
                                    .map(move |x| Term::new(term.c.clone(), x.clone()))
                            })
                            .collect(),
                    },
                    ..con
                })
            })
            .unwrap();

        println!("pb_model = {pb_model}");
        self.pb_model = Some((pb_model, pb_vars));
    }

    pub fn encode(
        &mut self,
        experiment: &Experiment,
        encode_record: &mut EncodeRecord,
        encode_record_path: Option<&PathBuf>,
        aux_out: Option<&PathBuf>,
    ) -> Result<Cnf, EncodeErr> {
        let enc_timer = Instant::now();
        let (enc_res, cnf) = match &experiment.system {
            System::Pbc => {
                let mut cnf = Cnf::new(0);
                // model.propagate(&Consistency::Bounds);

                let model = if experiment.con_encoding == ConEncoding::Ignore {
                    self.pbify();
                    &mut self.pb_model.as_mut().unwrap().0
                } else {
                    &mut self.model
                };

                model.encode_vars(&mut cnf).unwrap();
                if experiment.split_eq {
                    model.cons = model
                        .cons
                        .clone()
                        .into_iter()
                        .flat_map(|con| match con.cmp {
                            Comparator::Equal => {
                                vec![
                                    Lin {
                                        cmp: Comparator::LessEq,
                                        ..con.clone()
                                    },
                                    Lin {
                                        cmp: Comparator::GreaterEq,
                                        ..con
                                    },
                                ]
                            }
                            _ => vec![con],
                        })
                        .collect();
                }
                // TODO assuming we are not running out of time at this point

                encode_record.principal = Some(model.lits() as Lit);
                self.principal = encode_record.principal;
                // encode_record.obj = Some(Obj::Satisfy);

                write_stats(&encode_record, encode_record_path.cloned(), None);

                if true {
                    (
                        model
                            .encode(&mut cnf)
                            .map_err(|_| EncodeErr::Unsatisfiable)
                            .map(|_| ()),
                        cnf,
                    )
                } else {
                    let enc_res = model.constraints().try_for_each(|con| {
                        con.encode(&mut cnf, &experiment.model_config)
                            .map_err(|_| EncodeErr::Unsatisfiable)?;
                        check_enc_timer(self.enc_timeout, enc_timer)?;
                        Ok(())
                    });

                    (enc_res, cnf)
                }
            }
            System::MiniZinc => {
                // encode_record.obj = Some(Obj::Satisfy);
                let mut mzn = aux_out.cloned().unwrap();
                mzn.set_extension("picat.mzn");
                self.minizinc(&mzn).unwrap();
                let mut fzn = mzn.clone();
                fzn.set_extension("fzn");
                cmd(
                    &format!(
                        "minizinc -c --solver ./bin/solvers/picat.msc {} --fzn {}",
                        mzn.display(),
                        fzn.display()
                    ),
                    &[],
                );

                let mut dimacs = fzn.clone();
                dimacs.set_extension("dimacs");

                let out = cmd(
                    &format!(
                        "./bin/Picat/picat ./bin/Picat/fzn_picat/fzn_picat_sat.pi -e {} {}",
                        dimacs.display(),
                        fzn.display()
                    ),
                    &[],
                );
                if out.contains("UNSATISFIABLE") {
                    // in case picat-sat propagates unsat
                    assert!(!dimacs.exists());
                    let enc_time = enc_timer.elapsed().as_secs_f32();
                    encode_record.time = Some(enc_time);
                    println!("Done {}: {:?}", experiment, encode_record.statics);
                    write_stats(&encode_record, encode_record_path.cloned(), None);
                    return Err(EncodeErr::Unsatisfiable);
                }
                let cnf = Cnf::<Lit>::from_file(&dimacs).unwrap();
                encode_record.dimacs = Some(dimacs);

                encode_record.principal = Some(cnf.variables() as Lit);
                self.principal = encode_record.principal;
                // encode_record.obj = Some(Obj::Satisfy);
                write_stats(&encode_record, encode_record_path.cloned(), None);

                (Ok(()), cnf)
            }
            System::SavileRow | System::SavileRowBasic => {
                let (_, dimacs, _, _, _) = self.essence(
                    experiment,
                    None, // pass no sat cmd to only encode!
                    aux_out.cloned(),
                )?;

                let cnf = Cnf::<Lit>::from_file(dimacs.as_ref().unwrap()).unwrap();
                // TODO apparently this is trivial sat
                if cnf.variables() == 0 {
                    // SavileRow outputs empty formula for propagated unsat
                    let enc_time = enc_timer.elapsed().as_secs_f32();
                    encode_record.time = Some(enc_time);
                    println!("Done {}: {:?}", experiment, encode_record.statics);
                    write_stats(&encode_record, encode_record_path.cloned(), None);
                    return Err(EncodeErr::Error(String::from("Trivial SAT (presumably)")));
                }
                encode_record.dimacs = dimacs;
                // ilp.check(&int_assignment.as_ref().unwrap()).unwrap();
                (Ok(()), cnf)
                // (
                //     experiment,
                //     vec![int_assignment.unwrap().into_values().collect::<Vec<_>>()],
                // )
            }
            System::Scop => {
                #[cfg(not(debug_assertions))]
                let id = rand_id();
                #[cfg(debug_assertions)]
                let id = String::from("dev");

                let xcsp = format!("/tmp/scop-{}.xcsp", id);
                let xcsp = Path::new(&xcsp);
                self.to_xcsp(xcsp).unwrap();

                let encoding = match experiment.model_config.cutoff {
                    Some(0) => "-log",
                    Some(1) => "-both",
                    None => "-order",
                    Some(cutoff) => unreachable!("Only set cutoff=1 but was {cutoff}"),
                };

                // put file in dir, later rename to aux_out
                let aux_out = aux_out
                    .cloned()
                    .unwrap_or_else(|| PathBuf::from_str(&format!("/tmp/{}", id)).unwrap())
                    .with_extension("scop.dimacs");

                let aux_out_dir = aux_out.parent().unwrap();
                let out = String::from_utf8(
                    Command::new("java")
                        .arg("-jar")
                        .arg("./bin/scop-for-xcsp18-180731/scop.jar")
                        .arg("-tmp")
                        .arg(aux_out_dir)
                        .arg("-keep")
                        .arg(encoding) // -both, -order, -log
                        .arg(xcsp)
                        .stdout(Stdio::piped())
                        .output()
                        .unwrap()
                        .stdout,
                )
                .unwrap();

                let mut pid = "";
                for line in out.lines() {
                    match line.split_whitespace().collect::<Vec<_>>().as_slice() {
                        ["c", "PID:", pid_] => pid = pid_,
                        ["s", "UNSATISFIABLE"] => {
                            let enc_time = enc_timer.elapsed().as_secs_f32();
                            encode_record.time = Some(enc_time);
                            write_stats(&encode_record, encode_record_path.cloned(), None);
                            return Err(EncodeErr::Unsatisfiable);
                        }
                        _ => {}
                    }
                }

                assert!(!pid.is_empty(), "No PID found in SCOP output");

                let aux_out_file = [
                    aux_out_dir,
                    &PathBuf::from(format!("scop-{id}.xcsp-scop-{pid}.cnf")),
                ]
                .iter()
                .cloned()
                .collect::<PathBuf>();

                std::fs::rename(aux_out_file, &aux_out).unwrap();

                let cnf = Cnf::from_file(&aux_out).unwrap();

                (Ok(()), cnf)
            }
            e => todo!("Implement system {:?}", e),
        };

        encode_record.statics = Some(StaticsRecord::from(&cnf));

        // encode_record.pb_statics = Some(encoder.enc.pb_statics.clone());
        let enc_time = enc_timer.elapsed().as_secs_f32();
        encode_record.time = Some(enc_time);
        println!("Done {}: {:?}", experiment, encode_record);
        write_stats(&encode_record, encode_record_path.cloned(), None);
        enc_res.map(|()| cnf)
    }

    pub fn solve(
        &self,
        sat_cmd: String,
        obj: &Obj<Lit, C>,
        solve_seed: usize,
        last_var: Option<Lit>,
        aux_out: Option<PathBuf>,
        dimacs: Option<PathBuf>,
        remove_dimacs: bool,
    ) -> SolveRecord {
        let last_var = last_var.unwrap_or(self.wcnf.variables() as Lit);
        if sat_cmd != *"pbc" {
            let sat_cmd = std::path::PathBuf::from_str(&sat_cmd).unwrap();
            let dimacs = dimacs.unwrap_or_else(|| {
                let dimacs = aux_out
                    .map(|mut aux_out: PathBuf| {
                        aux_out.set_extension("dimacs");
                        aux_out
                    })
                    .unwrap();

                if obj.is_satisfy() {
                    Cnf::try_from(self.wcnf.clone())
                        .unwrap()
                        .to_file(&dimacs, None)
                        .unwrap();
                } else {
                    self.wcnf.to_file(&dimacs, None).unwrap();
                };
                dimacs
            });

            let solve_record = Self::solve_cmd(
                dimacs.clone(),
                sat_cmd,
                self.solver_timeout,
                solve_seed,
                last_var,
                obj,
            );
            if remove_dimacs {
                remove_file(dimacs).unwrap();
            }
            return solve_record;
        }
        if self.wcnf.clauses() == 0 {
            return SolveRecord {
                status: Status::Sat,
                solution: Some((1..=last_var).map(|l| -l).collect()),
                check: Some(Ok(())),
                ..Default::default()
            };
        }
        unimplemented!()
        /*
        unsafe {
            let timer = Instant::now();

            if let Some(timeout) = self.solver_timeout {
                #[repr(C)]
                pub struct State {
                    timer: Instant,
                    timeout: f32,
                }

                ipasir_set_terminate(
                    self.solver,
                    &mut State { timer, timeout } as *mut _ as *mut c_void,
                    Some(callback),
                );

                extern "C" fn callback(state: *mut c_void) -> i32 {
                    let State { timer, timeout } = unsafe { &mut *(state as *mut State) };
                    (timer.elapsed() > Duration::from_secs_f32(*timeout)) as i32
                }
            }

            let status = ipasir_solve(self.solver);
            let time = timer.elapsed().as_secs_f32();
            match status {
                0 => SolveRecord {
                    time,
                    check: Some(Ok(())),
                    ..Default::default()
                },
                10 => {
                    let solution = Some(
                        (1..=last_var)
                            .map(|x| {
                                ipasir_val(self.solver, x)
                                // TODO find better way to check this
                                // assert!(val.abs() == x);
                            })
                            .collect(),
                    );

                    let status = Status::Sat;
                    SolveRecord {
                        status,
                        solution,
                        time,
                        ..Default::default()
                    }
                }
                20 => SolveRecord {
                    status: Status::Unsat,
                    time,
                    ..Default::default()
                },
                status => SolveRecord {
                    status: Status::Error(EncodeErr::Error(format!("Unexpected status {status}"))),
                    time,
                    check: Some(Err(String::from("Unexpected status"))),
                    ..Default::default()
                },
            }
        }
        */
    }

    pub fn encode_linear(
        &mut self,
        encoder: &mut LinearEncoder<PbcEncoder>,
        linear: LinearConstraint<Lit, C>,
        opb_only: bool,
    ) -> Result<(), Unsatisfiable> {
        if !opb_only {
            encoder.encode(self, &linear)?;
        }
        self.pbs.push(linear);
        Ok(())
    }

    pub fn essence(
        &self,
        experiment: &Experiment,
        sat_cmd: Option<PathBuf>,
        aux_out: Option<PathBuf>,
    ) -> Result<
        (
            f32,
            Option<PathBuf>,
            Option<StaticsRecord>,
            Vec<SolveRecord>,
            Option<HashMap<IntVarId, C>>,
        ),
        EncodeErr,
    > {
        let remove_files = false;
        if matches!(experiment.int_encoding, IntEncoding::Ord | IntEncoding::Bin)
            || matches!(experiment.con_encoding, ConEncoding::Ignore)
            || matches!(experiment.add_consistency, AddConsistency::Aux)
        {
            panic!("Unsupported by SavileRow");
        }

        let (eprime, dimacs, sol_path, stats_path, infor_path) = if let Some(aux_out) = aux_out {
            (
                format!("{}.essence.eprime", aux_out.to_str().unwrap()),
                format!("{}.essence.dimacs", aux_out.to_str().unwrap()),
                format!("{}.essence.solution", aux_out.to_str().unwrap()),
                format!("{}.essence.info", aux_out.to_str().unwrap()),
                format!("{}.essence.infor", aux_out.to_str().unwrap()),
            )
        } else {
            let id = rand_id();
            (
                format!("/tmp/ilp-{id}.essence.eprime"),
                format!("/tmp/ilp-{id}.essence.dimacs"),
                format!("/tmp/ilp-{id}.essence.solution"),
                format!("/tmp/ilp-{id}.essence.info"),
                format!("/tmp/ilp-{id}.essence.infor"),
            )
        };

        let mut output = File::create(&eprime)?;

        let int_vars = self.model.vars();
        // TODO ???
        // assert!(
        //     int_vars.iter().all(
        //         |int_var| int_var.borrow().dom.iter().collect::<HashSet<_>>()
        //             == int_vars.first().unwrap().borrow().dom.iter().collect()
        //     ),
        //     "All variables must have the same domain for essence"
        // );

        writeln!(output, "language ESSENCE' 1.0")?;
        writeln!(
            output,
            "letting DOMS be domain int({})",
            int_vars.first().unwrap().borrow().dom.iter().join(",")
        )?;
        writeln!(
            output,
            "find xs : matrix indexed by [int(1..{})] of DOMS",
            int_vars.len()
        )?;
        let write_terms = |exp: &IntLinExp<Lit, C>| {
            let it = exp
                .terms
                .iter()
                // .zip(lin.coefs.iter())
                .map(|term| format!("{}*xs[{}]", term.c, term.x.borrow().id));

            Itertools::intersperse(it, " + ".to_string()).collect::<String>()
        };
        match &self.model.obj {
            Obj::Minimize(obj) | Obj::Maximize(obj) => {
                writeln!(
                    output,
                    "{} {}",
                    if self.model.obj.is_maximize() {
                        "maximising"
                    } else {
                        "minimising"
                    },
                    write_terms(obj)
                )
            }
            Obj::Satisfy => Ok(()),
        }?;

        writeln!(output, "such that")?;
        for il in self.model.constraints().with_position() {
            let (il, suffix) = match il {
                Position::Last(il) | Position::Only(il) => (il, ""),
                Position::First(il) | Position::Middle(il) => (il, ","),
            };
            let xs = write_terms(&il.exp);

            let cmp = match il.cmp {
                Comparator::LessEq => "<=",
                Comparator::Equal => "=",
                Comparator::GreaterEq => ">=",
            };
            let k = il.k;

            writeln!(output, "sum ([ {xs} ]) {cmp} {k}{suffix}",)?;
        }

        let pb_enc = match experiment.pb_encoding {
            PbEncoding::Gt => "-sat-pb-ggt",
            PbEncoding::Swc => "-sat-pb-swc",
            PbEncoding::Bdd => "-sat-pb-mdd",
            PbEncoding::Gpw => "-sat-pb-gpw",
            PbEncoding::Tree => "-sat-pb-tree",
            PbEncoding::Gmto => "-sat-pb-gmto",
            _ => panic!(),
        };

        let sum_enc = match experiment.pb_encoding {
            PbEncoding::Gt => "-sat-sum-ggt",
            PbEncoding::Swc => "-sat-sum-swc",
            PbEncoding::Bdd => "-sat-sum-mdd",
            PbEncoding::Gpw => "-sat-sum-gpw",
            PbEncoding::Tree => "-sat-sum-tree",
            PbEncoding::Gmto => "-sat-sum-gmto",
            _ => panic!(),
        };

        let enc_timeout = &format!("{}", self.enc_timeout.unwrap_or(0f32) as C);

        let mut cmd = Command::new("./bin/savilerow_1.9.2/savilerow");

        cmd.arg(&eprime)
            .arg("-sat")
            //.arg("-sat-amo-ladder")
            .arg(pb_enc)
            .arg(sum_enc)
            .arg("-opt-strategy")
            .arg("linear")
            .arg("-timelimit")
            .arg(enc_timeout)
            .arg("-out-sat")
            .arg(&dimacs)
            .arg("-out-info")
            .arg(&stats_path)
            .arg("-out-solution")
            .arg(&sol_path);

        if experiment.system == System::SavileRowBasic {
            cmd.arg("-O0").arg("-S0").arg("-no-cse");
        }

        if let Some(sat_cmd) = sat_cmd.clone() {
            cmd.arg("-run-solver")
                .arg("-sat-family")
                .arg("cadical")
                .arg("-satsolver-bin")
                .arg(&sat_cmd)
                .arg("-solver-options")
                .arg(&format!("-t {}", self.solver_timeout.unwrap_or(0f32) as C));
        }

        let output = cmd.output()?;

        let stderr = output
            .stderr
            .into_iter()
            .map(char::from)
            .collect::<String>();

        let stdout = output
            .stdout
            .into_iter()
            .map(char::from)
            .collect::<String>();

        if stderr.contains("ERROR: Savile Row timed out.") {
            return Err(EncodeErr::Timeout);
        }

        let (status, int_assignment, obj, check) = if sat_cmd.is_none() {
            (Status::Encoded, None, None, Some(Ok(())))
        } else if stdout.contains("SAT solver exited with error code:0")
            && stdout.contains("No solution found")
        {
            (Status::Unknown, None, None, Some(Ok(())))
        } else if stdout.contains("No solution found") {
            (Status::Unsat, None, None, None)
        } else {
            let int_assignment = &BufReader::new(File::open(sol_path.clone()).unwrap())
                .lines()
                .nth(1)
                .unwrap()
                .unwrap();
            if remove_files {
                remove_file(sol_path).unwrap();
            }
            let int_assignment = HashMap::<_, _>::from_iter(
                int_assignment[15..int_assignment.len() - 1]
                    .split(", ")
                    .enumerate()
                    .map(|(id, x)| (int_vars[id + 1].borrow().id, x.parse::<C>().unwrap())),
            );

            // let obj = ilp.obj.obj().map(|obj| obj.assign(&int_assignment));
            (Status::Sat, Some(int_assignment), None, None)
        };

        let (solve_time, enc_time, statics) = if sat_cmd.is_some() {
            let stats = &BufReader::new(File::open(stats_path.clone()).unwrap())
                .lines()
                .map(|x| x.unwrap())
                .collect::<Vec<String>>();

            if remove_files {
                remove_file(stats_path).unwrap();
                remove_file(infor_path).unwrap();
            }

            let stats = HashMap::<String, String>::from_iter(stats.iter().map(|line| {
                line.split(':')
                    .collect::<Vec<_>>()
                    .into_iter()
                    .map(|x| x.to_string())
                    .collect_tuple()
                    .unwrap()
            }));

            (
                stats["SolverTotalTime"].parse().unwrap(),
                stats["SavileRowTotalTime"].parse::<f32>().unwrap(),
                StaticsRecord {
                    vars: stats["SATVars"].parse::<usize>().unwrap(),
                    cls: stats["SATClauses"].parse::<usize>().unwrap(),
                    lits: 0,
                },
            )
        } else {
            let cnf = Cnf::<Lit>::from_file(&PathBuf::from_str(&dimacs).unwrap()).unwrap();

            (
                0.0,
                0.0,
                StaticsRecord {
                    vars: cnf.variables(),
                    cls: cnf.clauses(),
                    lits: cnf.literals(),
                },
            )
        };

        println!("ENCODED: {} in {:?} ({:?})", experiment, enc_time, statics,);

        let solve_records = if sat_cmd.is_some() {
            vec![SolveRecord {
                status,
                time: solve_time,
                cost: obj,
                check,
                ..SolveRecord::default()
            }]
        } else {
            vec![]
        };

        for solve_record in &solve_records {
            println!("STATUS: {}", solve_record);
        }

        // Note dimacs is auto-deleted if we are solving
        let dimacs = sat_cmd
            .is_none()
            .then_some(PathBuf::from_str(&dimacs).unwrap());

        Ok((
            enc_time,
            dimacs,
            Some(statics),
            solve_records,
            int_assignment,
        ))
    }

    pub fn merge_in(&mut self, other: Cnf<Lit>) -> Result {
        let last_var = self.wcnf.variables();
        let new_vars = other.variables() - last_var;
        for _ in last_var..new_vars {
            self.new_var();
        }
        for clause in other.iter() {
            self.add_clause(clause)?;
        }
        Ok(())
    }

    pub fn minizinc(&self, mzn: &PathBuf) -> Result<(), std::io::Error> {
        let mut output = File::create(mzn)?;

        for x in self.model.vars() {
            let dom = &x.borrow().dom;
            let dom = if dom.size() == dom.ub() - dom.lb() + 1 {
                format!("{}..{}", dom.lb(), dom.ub())
            } else {
                format!("{{{}}}", dom.iter().join(","))
            };
            writeln!(output, "var {}: x{};", dom, x.borrow().id)?;
        }

        let suffix = ";";
        for il in self.model.constraints() {
            let xs = {
                let it = il
                    .exp
                    .terms
                    .iter()
                    .map(|Term { x, c }| format!("{}*x{}", c, x.borrow().id));

                Itertools::intersperse(it, " + ".to_string()).collect::<String>()
            };

            let cmp = match il.cmp {
                Comparator::LessEq => "<=",
                Comparator::Equal => "==",
                Comparator::GreaterEq => ">=",
            };
            let k = il.k;

            writeln!(output, "constraint {xs} {cmp} {k}{suffix}",)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum EncodeErr {
    Unsatisfiable,
    Timeout,
    Memory,
    Error(String),
}

impl Display for EncodeErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodeErr::Unsatisfiable => write!(f, "UNSAT"),
            EncodeErr::Timeout => write!(f, "TIMEOUT"),
            EncodeErr::Memory => write!(f, "MEM"),
            EncodeErr::Error(s) => write!(f, "Err: {s}"),
        }
    }
}

impl From<std::io::Error> for EncodeErr {
    fn from(value: std::io::Error) -> Self {
        Self::Error(value.to_string())
    }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Status {
    Opt,
    Sat,
    Unsat,
    #[default]
    Unknown,
    Skipped,
    Encoded,
    Error(EncodeErr),
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Opt => write!(f, "Opt"),
            Self::Sat => write!(f, "Sat"),
            Self::Unsat => write!(f, "Unsat"),
            Self::Unknown => write!(f, "Unknown"),
            Self::Encoded => write!(f, "Encoded"),
            Self::Skipped => write!(f, "Skipped"),
            Self::Error(err) => write!(f, "Unexpected({:?})", err),
        }
    }
}

impl ClauseDatabase for Formula {
    type Lit = Lit;

    fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
        const DETECT_DUPLICATE_CLAUSES: bool = false;
        if !DETECT_DUPLICATE_CLAUSES || self.wcnf.iter().any(|c| c.0 == cl) {
            // for c in cl {
            //     unsafe {
            //         ipasir_add(self.solver, *c);
            //     }
            // }
            // unsafe {
            //     ipasir_add(self.solver, 0);
            // }
            self.wcnf.add_weighted_clause(cl, None)?;
        } else {
            println!("DUPLICATE clause {:?}", cl);
        }

        Ok(())
    }

    fn new_var(&mut self) -> Self::Lit {
        self.wcnf.new_var()
    }
}
