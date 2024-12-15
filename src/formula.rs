use crate::cli::{ConEncoding, Experiment, IntEncoding, PbEncoding, SolveRecord, StaticsRecord};
use crate::cli::{EncodeRecord, System};
use crate::slurm::cmd;
use crate::{check_enc_timer, write_stats};
use pindakaas::bool_linear::{BoolLinExp, Comparator};
use pindakaas::integer::{Assignment, IntVarRef, Lin, LinExp, MapSol, Mix, Model, Obj, Term};
use pindakaas::solver::cadical::Cadical;
use pindakaas::solver::SlvTermSignal;
use pindakaas::solver::Solver;
use pindakaas::solver::TermCallback;
use pindakaas::VarRange;
use pindakaas::Wcnf;
use pindakaas::{CheckError, ClauseDatabase, Cnf, Lit, Valuation, Var};
use pindakaas::{Result, Unsatisfiable};
use std::fmt::{self, Display};
use std::io::Write;
use std::path::PathBuf;

use std::num::NonZeroI32;

use itertools::{Itertools, Position};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

use std::fs::File;
use std::fs::{self, remove_file};
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::process::{Command, Stdio};

use crate::rand_id;

use std::collections::{HashMap, HashSet};
use std::time::Instant;

pub type C = i64;
pub type Seed = u64;

pub struct Formula {
    pub(crate) model: Model,
    pub(crate) wcnf: Wcnf,
    pub(crate) solver_timeout: Option<f32>,
    pub(crate) enc_timeout: Option<f32>,
    pub(crate) labels: HashMap<Lit, String>,
    mem: Option<f32>,
}

impl Formula {
    pub fn new(
        model: Model,
        solver_timeout: Option<f32>,
        enc_timeout: Option<f32>,
        mem: Option<f32>,
    ) -> Self {
        Self {
            model,
            wcnf: Wcnf::default(),
            // pb_model: None,
            // solver: unsafe { ipasir_init() },
            // pbs: vec![],
            solver_timeout,
            enc_timeout,
            labels: HashMap::new(),
            mem,
        }
    }

    pub fn to_xcsp(&self, path: &Path) -> Result<(), std::io::Error> {
        let mut output = File::create(path)?;
        writeln!(output, "<instance>")?;
        writeln!(output, "<variables>")?;

        self.model.vars().try_for_each(|x| {
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

        for il in self.model.constraints() {
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

    /*
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
                    Comparator::LessEq => "<=",
                    Comparator::Equal => "=",
                    Comparator::GreaterEq => ">=",
                },
                pb.k - pb.exp.add,
            )?;
        }
        Ok(())
    }
    */

    pub fn stats(&self) -> StaticsRecord {
        StaticsRecord::new(
            self.wcnf.variables(),
            self.wcnf.clauses(),
            self.wcnf.literals(),
        )
    }

    /*
    pub fn assign(&self, lit_assignment: &[Lit]) -> Result<Assignment, CheckError> {
        let sol = MapSol::from(lit_assignment.to_vec());
        if let Some((pb_model, pb_vars)) = self.pb_model.as_ref() {
            // let pb_var_assignment = pb_model.assign(MapSol::from(lit_assignment.iter().map())?;
            let pb_var_assignment = pb_model.assign(&sol)?;
            Ok(Assignment(
                pb_vars
                    .iter()
                    .map(|(int_var_id, pb_vars)| {
                        (
                            *int_var_id,
                            (
                                String::from("todo lbl"),
                                pb_vars
                                    .iter()
                                    .map(|pb_var| pb_var_assignment[&pb_var.borrow().id].1)
                                    .sum(),
                            ),
                        )
                    })
                    .collect(),
            ))
        } else {
            self.model.assign(&sol)
        }
    }

    pub fn assign_lits(&self, model: &[Lit]) -> HashMap<Var, bool> {
        HashMap::from_iter(model.iter().map(|x| (x.var(), !x.is_negated())))
    }

    pub fn add_weighted_clause(&mut self, cl: &[Lit], weight: C) -> Result {
        self.wcnf
            .add_weighted_clause(cl.iter().copied(), Some(weight))
    }

    pub fn solver_name(sat_cmd: &Path) -> &str {
        sat_cmd.file_name().unwrap().to_str().unwrap()
    }
    */

    //     pub fn solve_cmd(
    //         path: PathBuf,
    //         _solver_timeout: Option<f32>, // TODO
    //         _solve_seed: usize,           // TODO
    //         last_var: Var,
    //     ) -> SolveRecord {

    //         // TODO move to pindakaas as CLISolver
    //         /*
    //         let solver_name = Self::solver_name(&sat_cmd);
    //         assert!(sat_cmd.exists());
    //         assert!(path.exists(), "DIMACS does not exist at: {path:?}");
    //         assert!([
    //             "kissat",
    //             "cadical",
    //             "open-wbo",
    //             "open-wbo-inc",
    //             "glucose_static",
    //             "glucose-simp"
    //         ]
    //         .contains(&solver_name));
    //         let mut cost: Option<C> = None;
    //         let mut status: Option<Status> = None;
    //         let mut solution: Vec<Lit> = vec![];
    //         let solve_timer = Instant::now();

    //         let mut args = vec![];
    //         args.push(format!("{}", path.display()));

    //         if let Some(time) = solver_timeout {
    //             match solver_name {
    //                 "kissat" => {
    //                     assert!(obj.is_satisfy());
    //                     args.push(format!("--seed={solve_seed}"));
    //                     args.push(format!("--time={}", time));
    //                     status = Some(Status::Unknown); // kissat doesn't s-line on timeout
    //                 }
    //                 "cadical" => {
    //                     assert!(obj.is_satisfy());
    //                     args.push(format!("--seed={solve_seed}"));
    //                     args.push(String::from("-t"));
    //                     args.push(format!("{}", solver_timeout.unwrap()));
    //                 }
    //                 "open-wbo" => {
    //                     assert!(obj.is_satisfy());
    //                     let algorithm = 1;
    //                     args.push(format!("-algorithm={}", algorithm));
    //                     args.push(format!("-cpu-lim={}", time));
    //                     args.push(format!("-rnd-seed={solve_seed}"));
    //                 }
    //                 "glucose_static" | "glucose-simp" => {
    //                     assert!(obj.is_satisfy());
    //                     // args.push(format!("-algorithm={}", algorithm));
    //                     args.push(format!("-cpu-lim={}", time));
    //                     args.push(format!("-rnd-seed={solve_seed}"));
    //                     args.push(String::from("-model"));
    //                     // let verb = 1;
    //                     // args.push(format!("-verb={}", verb));
    //                 }
    //                 "open-wbo-inc" => {
    //                     assert!(!obj.is_satisfy());
    //                     args.push(format!("-rnd-seed={solve_seed}"));
    //                 }
    //                 slv => unreachable!("Unverified solver: {}", slv),
    //             };
    //         }

    //         println!("Running SAT cmd: {} {}", &sat_cmd.display(), args.join(" "));

    //         let output = Command::new(sat_cmd).args(args).output().unwrap();

    //         if output.status.code().unwrap_or(-1) == -1 {
    //             let out = String::from_utf8(output.stdout).unwrap();
    //             let err = String::from_utf8(output.stderr).unwrap();
    //             panic!("{}\n{}\n", out, err);
    //         }

    //         for line in String::from_utf8(output.stdout.clone()).unwrap().lines() {
    //             let mut tokens = line.split_whitespace();
    //             match tokens.next() {
    //                 None | Some("c") => {
    //                     if let Some("UNKNOWN") = tokens.next() {
    //                         status = Some(Status::Unknown)
    //                     } else {
    //                         continue;
    //                     }
    //                 }
    //                 Some("o") => cost = Some(tokens.next().unwrap().parse().unwrap()),
    //                 Some("s") => match tokens.next() {
    //                     Some("OPTIMUM") => status = Some(Status::Opt),
    //                     Some("SATISFIABLE") => status = Some(Status::Sat),
    //                     Some("UNSATISFIABLE") => status = Some(Status::Unsat),
    //                     Some("UNKNOWN") | Some("INDETERMINATE") => status = Some(Status::Unknown),
    //                     status => panic!("Unknown status: {status:?}"),
    //                 },
    //                 Some("v") => {
    //                     tokens
    //                         .filter(|&t| (t != "0"))
    //                         .map(|t| {
    //                             Lit(t
    //                                 .parse::<NonZeroI32>()
    //                                 .unwrap_or_else(|t| panic!("parsing v line error: {t} in {line}")))
    //                         })
    //                         .filter(|t| t.var() <= last_var)
    //                         .for_each(|lit| {
    //                             solution.push(lit);
    //                         });
    //                 }
    //                 line => panic!("Unexpected slv output: {:?}", line),
    //             }
    //         }
    //         let solve_time = solve_timer.elapsed().as_secs_f32();
    //         let status = status.unwrap_or_else(|| {
    //             panic!(
    //                 "No status set in SAT output:
    //                 {}
    //                 \n
    //                 {}
    //                 ",
    //                 String::from_utf8(output.stdout).unwrap(),
    //                 std::fs::read_to_string(path).unwrap()
    //             )
    //         });
    //         let solution = matches!(status, Status::Sat | Status::Opt).then(|| solution);

    //         SolveRecord {
    //             status,
    //             solution,
    //             time: solve_time,
    //             cost,
    //             ..SolveRecord::default()
    //         }
    //         */
    //     }

    /*
    pub fn write(&self, aux_out: Option<PathBuf>, obj: &Obj) -> PathBuf {
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
    */

    //     println!("pb_model = {pb_model}");
    //     self.pb_model = Some((pb_model, pb_vars));
    // }

    pub fn encode(
        &mut self,
        experiment: &Experiment,
        encode_record: &mut EncodeRecord,
        aux_out: Option<PathBuf>,
    ) -> Result<Cnf, EncodeErr> {
        const SAVE_DIMACS: bool = cfg!(debug_assertions);

        let aux_out = aux_out.unwrap_or_else(|| {
            if cfg!(debug_assertions) {
                PathBuf::from(format!("/tmp/{}", rand_id()))
            } else {
                PathBuf::from("dev")
            }
        });

        let cnf_res = match &experiment.system {
            System::Pbc => {
                // model.propagate(&Consistency::Bounds);

                let mut cnf = Cnf::default();
                // model.encode_vars(&mut cnf).unwrap();
                let model = if experiment.split_eq {
                    Model {
                        cons: self
                            .model
                            .cons
                            .iter()
                            .cloned()
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
                            .collect(),
                        ..self.model.clone()
                    }
                } else {
                    self.model.clone()
                };

                let mut model = if experiment.con_encoding == ConEncoding::Ignore {
                    model.pbify(&mut cnf)?
                } else {
                    model.clone()
                };
                model
                    .encode_pub(&mut cnf)
                    .map_err(|_| EncodeErr::Trivial(false))
                    .map(|_decomp| {
                        #[cfg(debug_assertions)]
                        println!("decomp = {}", _decomp);

                        if SAVE_DIMACS {
                            let mut dimacs = String::from(aux_out.clone().to_str().unwrap());
                            dimacs.push_str(".pbc.dimacs");
                            encode_record.dimacs = Some(PathBuf::from(&dimacs));
                        }
                        Ok(cnf)
                    })?
            }
            System::MiniZinc => {
                // encode_record.obj = Some(Obj::Satisfy);
                let enc_timer = Instant::now();
                let mut mzn = aux_out.clone();
                mzn.set_extension("picat.mzn");
                self.minizinc(&mzn).unwrap();
                let mut fzn = mzn.clone();
                fzn.set_extension("fzn");
                cmd(
                    &format!(
                        "minizinc -c --solver ./bin/fzn_picat/picat.msc {} --fzn {}",
                        mzn.display(),
                        fzn.display(),
                    ),
                    &[],
                    self.enc_timeout,
                )
                .unwrap();
                println!("Flattening done @{}s", enc_timer.elapsed().as_secs_f32());

                let mut dimacs = fzn.clone();
                dimacs.set_extension("dimacs");

                let (out, _) = cmd(
                    &format!(
                        "./bin/fzn_picat/Picat/picat ./bin/fzn_picat/fzn_picat_sat.pi -e {} {}",
                        dimacs.display(),
                        fzn.display()
                    ),
                    &[],
                    self.enc_timeout
                        .map(|t| t - enc_timer.elapsed().as_secs_f32()),
                )?;
                println!(
                    "Picat encoding done @{}s",
                    enc_timer.elapsed().as_secs_f32()
                );

                #[cfg(debug_assertions)]
                println!("{out}");

                // may or may not
                if dimacs.exists() {
                    encode_record.dimacs = Some(dimacs);
                }

                if out.contains("UNSATISFIABLE") {
                    return Err(EncodeErr::Trivial(false));
                } else {
                    Ok(Cnf::from_file(encode_record.dimacs.as_ref().unwrap()).unwrap())
                }
            }
            System::SavileRow | System::SavileRowBasic => {
                const SR_SOLVE: bool = false;
                let dimacs = self.essence(experiment, aux_out.clone(), SR_SOLVE)?;
                let cnf = Cnf::from_file(&dimacs).unwrap();
                encode_record.dimacs = Some(dimacs);
                Ok(cnf)
            }
            System::Scop => {
                let aux_out_str = aux_out.display();
                let (dimacs, xcsp, _stdout, _stderr) = (
                    format!("{}.scop.dimacs", aux_out_str),
                    format!("{}.scop.xcsp", aux_out_str),
                    format!("{}.scop.stdout", aux_out_str),
                    format!("{}.scop.stderr", aux_out_str),
                );

                self.to_xcsp(Path::new(&xcsp)).unwrap();

                let encoding = match experiment.model_config.cutoff {
                    Mix::Binary => "-log",
                    Mix::Mix(1) => "-hybrid",
                    Mix::Mix(cutoff) => unreachable!("Only set cutoff=1 but was {cutoff}"),
                    Mix::Order => "-order",
                };

                let mem = self
                    .mem
                    .map(|mem| (1000000.0 * mem).round()) // to kb
                    .map(|mem| format!("-Xmx{mem}k -Xmx{mem}k"))
                    .unwrap_or_default();

                let (out,_) = cmd(&format!("java {mem} -Xss128m -cp ./bin/fun-scop/scop.jar fun.scop.launcher.XCSP19Encode {encoding} -tmp {} {xcsp}", aux_out.parent().unwrap().display()), &[], self.enc_timeout)?;

                let mut pid = "";
                for line in out.lines() {
                    match line.split_whitespace().collect::<Vec<_>>().as_slice() {
                        ["c", "PID:", pid_] => pid = pid_,
                        ["s", "UNSATISFIABLE"] => {
                            return Err(EncodeErr::Trivial(false));
                        }
                        ["s", "UNSUPPORTED"] => {
                            // means encoding is done (with no solver specified)
                            break;
                        }
                        _ => continue,
                    }
                }

                assert!(
                    !pid.is_empty(),
                    "No PID found in SCOP output:{out}
                    "
                );

                let mut scop_cnf = aux_out.clone();
                scop_cnf.set_extension(format!("scop.xcsp-scop-{pid}.cnf"));

                std::fs::rename(scop_cnf, dimacs.clone()).expect(&out);
                encode_record.dimacs = Some(PathBuf::from(dimacs.clone()));

                let cnf = Cnf::from_file(encode_record.dimacs.as_ref().unwrap()).unwrap();
                Ok(cnf)
            }
            e => todo!("Implement system {:?}", e),
        };

        if let Some(dimacs) = encode_record.dimacs.as_mut() {
            if dimacs.exists() && !SAVE_DIMACS {
                remove_file(dimacs).unwrap();
                encode_record.dimacs = None;
            } else if SAVE_DIMACS {
                // does not exist, create!
                // if doesn't exist, create with lp as comment!
                if let Ok(cnf) = cnf_res.as_ref() {
                    cnf.to_file(dimacs, Some(&format!("{}\n{}", experiment, self.model)))?;
                }
            } else {
                encode_record.dimacs = None;
            }
        }

        if let Ok(cnf) = cnf_res.as_ref() {
            match StaticsRecord::from(cnf) {
                StaticsRecord {
                    vars: 0,
                    cls: 0,
                    lits: 0,
                } => Err(EncodeErr::Trivial(true)),
                StaticsRecord {
                    vars: 0,
                    cls: 1,
                    lits: 0,
                } => Err(EncodeErr::Trivial(false)),
                _ => cnf_res,
            }
        } else {
            cnf_res
        }
    }

    pub fn solve(
        &self,
        _solve_seed: usize, // TODO
        last_var: Option<Var>,
        experiment: &Experiment,
    ) -> SolveRecord {
        println!("SOLVE T/O {:?}", self.solver_timeout);
        // TODO set timeout
        let vars = last_var
            .map(|last_var| VarRange::new(Var::from(1), last_var))
            .unwrap_or(if self.wcnf.variables() == 0 {
                VarRange::empty()
            } else {
                VarRange::new(Var::from(1), Var::from(self.wcnf.variables() as i32))
            });

        let cnf = Cnf::from(self.wcnf.clone());
        // TODO pindakaas-cadical is failing on the unsat (0 vars, >0 clauses), so returning res directly
        if vars.is_empty() {
            return SolveRecord {
                solution: Some(MapSol::default()),
                status: if cnf.clauses() == 0 {
                    Status::Sat
                } else {
                    Status::Unsat
                },
                ..SolveRecord::default()
            };
        }

        let mut slv = Cadical::default();
        // TODO consider add_cnf part of solving? For now no b/c it SEGVAULTs actually..
        slv.add_cnf(cnf);

        let solve_timer = Instant::now();
        if let Some(solver_timeout) = self.solver_timeout {
            // println!("set callback: {}", solver_timeout);
            slv.set_terminate_callback(Some(move || {
                // println!("Solve time left: {}", solve_timer.elapsed().as_secs_f32());
                if solve_timer.elapsed().as_secs_f32() <= solver_timeout {
                    SlvTermSignal::Continue
                } else {
                    // println!("Term!");
                    SlvTermSignal::Terminate
                }
            }));
        }

        let sol_res = slv.solve();
        let time = solve_timer.elapsed().as_secs_f32();

        // back-up
        if self
            .solver_timeout
            .map(|solver_timeout| time > solver_timeout)
            .unwrap_or_default()
        {
            return SolveRecord {
                status: Status::Unknown,
                time,
                ..Default::default()
            };
        }

        let solve_record = match sol_res {
            SolveResult::Satisfied(sol) => {
                let sol = MapSol::new(vars, &sol);
                SolveRecord {
                    status: Status::Sat,
                    assignment: (experiment.system == System::Pbc).then(|| self.model.assign(&sol)),
                    solution: Some(sol),
                    time,
                    ..Default::default()
                }
            }
            SolveResult::Unsatisfiable(_) => SolveRecord {
                status: Status::Unsat,
                time,
                ..Default::default()
            },
            SolveResult::Unknown => SolveRecord {
                status: Status::Unsat,
                time,
                ..Default::default()
            },
        };

        println!("SOLVE DONE @{}", time);
        SolveRecord {
            time,
            ..solve_record
        }
    }

    // pub fn encode_linear(
    //     &mut self,
    //     encoder: &mut LinearEncoder<PbcEncoder>,
    //     linear: LinearConstraint,
    //     opb_only: bool,
    // ) -> Result<(), Unsatisfiable> {
    //     if !opb_only {
    //         encoder.encode(self, &linear)?;
    //     }
    //     self.pbs.push(linear);
    //     Ok(())
    // }

    pub fn essence(
        &self,
        experiment: &Experiment,
        aux_out: PathBuf,
        solve: bool,
    ) -> Result<PathBuf, EncodeErr> {
        if matches!(experiment.int_encoding, IntEncoding::Ord | IntEncoding::Bin)
            || matches!(experiment.con_encoding, ConEncoding::Ignore)
            || experiment.model_config.add_consistency
        {
            panic!("Unsupported by SavileRow");
        }

        let (eprime, dimacs, sol_path, stats_path, _infor_path) = {
            let aux_out = aux_out.display();
            (
                format!("{}.essence.eprime", aux_out),
                format!("{}.essence.dimacs", aux_out),
                format!("{}.essence.solution", aux_out),
                format!("{}.essence.info", aux_out),
                format!("{}.essence.infor", aux_out),
            )
        };

        let mut output = File::create(&eprime).unwrap();

        writeln!(output, "language ESSENCE' 1.0")?;
        for x in self.model.vars() {
            writeln!(
                output,
                "find {} : int({})",
                x.borrow().lbl(),
                x.borrow()
                    .dom
                    .ranges
                    .iter()
                    .map(|(l, u)| format!("{l}..{u}"))
                    .join(",")
            )?;
        }
        let write_terms = |exp: &LinExp| {
            let it = exp
                .terms
                .iter()
                .map(|term| format!("{}*{}", term.c, term.x.borrow().lbl()));

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

        let basic = if experiment.system == System::SavileRowBasic {
            "-O0 -S0 -no-cse"
        } else {
            ""
        };

        let envs = self
            .mem
            .map(|mem| {
                vec![(
                    "PBC_JAVA_MEM",
                    format!("-Xmx{}k", (1000000.0 * mem).round()),
                )]
            })
            .unwrap_or_default();

        let solve_arg = solve.then_some("-run-solver").unwrap_or_default();
        let enc_timer = Instant::now();
        cmd(&format!("./bin/savilerow/savilerow {eprime} -sat {pb_enc} {sum_enc} -out-sat {dimacs} -out-info {stats_path} -out-solution {sol_path} {solve_arg} {basic}"), &envs.iter().map(|x| (x.0, x.1.as_str())).collect_vec(), self.enc_timeout)?;
        println!("DONE {}, solve={solve}", enc_timer.elapsed().as_secs_f32());

        if solve {
            if PathBuf::from(&sol_path).exists() {
                let a = Assignment::from(
                    fs::read(sol_path)
                        .unwrap()
                        .lines()
                        .skip(1)
                        .map(
                            |l| match l.as_ref().unwrap().split_whitespace().collect_vec()[..] {
                                ["letting", x, "be", v] => {
                                    (self.model.var_by_lbl(x).unwrap(), v.parse::<C>().unwrap())
                                }
                                _ => panic!("{:?}", l),
                            },
                        )
                        .collect_vec(),
                );
                assert!(self.model.check_assignment(&a).is_ok());
                Err(EncodeErr::Trivial(true))
            } else {
                println!("solved: unsat");
                Err(EncodeErr::Trivial(false))
            }
        } else {
            Ok(dimacs.into())
        }
    }

    // pub fn merge_in(&mut self, other: Cnf) -> Result {
    //     let last_var = self.wcnf.variables();
    //     let new_vars = other.variables() - last_var;
    //     for _ in last_var..new_vars {
    //         self.new_var();
    //     }
    //     for clause in other.iter() {
    //         self.add_clause(clause.iter().cloned())?;
    //     }
    //     Ok(())
    // }

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
    Timeout,
    Memory,
    Trivial(bool),
    Error(String),
}

impl From<Unsatisfiable> for EncodeErr {
    fn from(_: Unsatisfiable) -> Self {
        Self::Trivial(false)
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
    Encoded,
    Error(EncodeErr),
}

impl From<bool> for Status {
    fn from(value: bool) -> Self {
        if value {
            Status::Sat
        } else {
            Status::Unsat
        }
    }
}

impl Display for System {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                System::Pbc => "",
                System::SavileRow => "Savile Row",
                System::Scop => "Fun-sCOP",
                System::MiniZinc => "Picat-SAT",
                s => todo!("{s:?}"),
            }
        )
    }
}

impl Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Opt => write!(f, "OPT"),
            Self::Sat => write!(f, "SAT"),
            Self::Unsat => write!(f, "UNS"),
            Self::Unknown => write!(f, "UNK"),
            Self::Encoded => write!(f, "ENC"),
            Self::Error(err) => write!(f, "{err}"),
        }
    }
}

impl Display for EncodeErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodeErr::Timeout => write!(f, "ETO"),
            EncodeErr::Memory => write!(f, "MEM"),
            EncodeErr::Trivial(sat) => write!(f, "{} (triv.)", Status::from(*sat)),
            EncodeErr::Error(s) => write!(f, "Err: {s}"),
        }
    }
}

use pindakaas::solver::SolveResult;
impl From<SolveResult<MapSol>> for Status {
    fn from(res: SolveResult<MapSol>) -> Self {
        match res {
            SolveResult::Satisfied(_) => Status::Sat,
            SolveResult::Unsatisfiable(_) => Status::Unsat,
            SolveResult::Unknown => Status::Unknown,
        }
    }
}

// impl ClauseDatabase for Formula {
//     fn add_clause<I: IntoIterator<Item = pindakaas::Lit>>(&mut self, cl: I) -> Result {
//         // const DETECT_DUPLICATE_CLAUSES: bool = false;
//         // if !DETECT_DUPLICATE_CLAUSES || self.wcnf.iter().any(|c| c.0 == cl) {
//         //     // for c in cl {
//         //     //     unsafe {
//         //     //         ipasir_add(self.solver, *c);
//         //     //     }
//         //     // }
//         //     // unsafe {
//         //     //     ipasir_add(self.solver, 0);
//         //     // }
//         //     self.wcnf.add_weighted_clause(cl, None)?;
//         // } else {
//         //     println!("DUPLICATE clause {:?}", cl);
//         // }

//         self.wcnf.add_weighted_clause(cl, None)?;

//         Ok(())
//     }

//     type CondDB = Self;
//     fn new_var(&mut self) -> Var {
//         self.wcnf.new_var()
//     }
// }
