#![allow(clippy::too_many_arguments, unused_imports, clippy::type_complexity)]
#![allow(dead_code)]
use cli::ConEncoding;
use cli::PbStaticsRecord;
use cli::StaticsRecord;
use core::ops::Range;
use formula::EncodeErr;
use formula::Seed;
use pindakaas::bool_linear::Comparator;
use serde::Deserialize;
use std::fmt::Display;

use itertools::Itertools;
use pindakaas::integer::Consistency;
use pindakaas::integer::Decomposer;
use pindakaas::integer::Lin;
use pindakaas::integer::LinExp;
use pindakaas::integer::Mix;
use pindakaas::integer::Model;
use pindakaas::integer::ModelConfig;
use pindakaas::integer::Term;
use pindakaas::solver::cadical::Cadical;
use pindakaas::Cnf;
use pindakaas::Wcnf;
use scm::scm;
use std::fs::remove_file;
use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;
use std::time::Duration;

use serde_json::to_writer_pretty;

use crate::{
    analyze::analyze,
    cli::{parse, EncodeRecord, Experiment, PbEncoding, Run, SolveRecord, System},
    formula::{Formula, Status, C},
};

use rand::distributions::{Distribution, Uniform};
use rand::{rngs::StdRng, SeedableRng};
use std::time::Instant;

mod analyze;
mod scm;
mod slurm;

mod cli;
mod formula;
// mod ilp;

#[derive(Default)]
enum Mode {
    #[default]
    Solve,
    Encode,
    Analyze,
}

const MODE: Mode = Mode::Solve;
// const MODE: Mode = Mode::Encode;
// const MODE: Mode = Mode::Setup;

impl Display for PbEncoding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            PbEncoding::Adder => "RCA".to_string(),
            PbEncoding::Tree => "Tree".to_string(),
            PbEncoding::BinaryMerger => todo!("Check how similar to which encoding this PBLib encoding is (I thought approx. GT?)"),
            _ => format!("{self:?}").to_uppercase()
        })
    }
}

impl Display for Experiment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cutoff = match self.model_config.cutoff {
            Mix::Order => "Ord".into(),
            Mix::Binary => "Bin".into(),
            Mix::Mix(_) if self.system == System::Scop => "".to_string(),
            Mix::Mix(c) => format!("Mix({c})"),
        };
        const SHORT: bool = true;

        let pb_enc = format!("{}", self.pb_encoding);
        let con_enc = (self.con_encoding == ConEncoding::Ignore)
            .then_some("PB")
            .unwrap_or_default();
        let split_eqs = self.split_eq.then_some("SPLIT").unwrap_or_default();
        let prop = (self.model_config.propagate == Consistency::Bounds)
            .then_some("Bounds")
            .unwrap_or_default();
        let feats = [&pb_enc, split_eqs, con_enc, &cutoff, prop]
            .into_iter()
            .filter(|f| !f.is_empty())
            .join(" + ");

        if SHORT {
            match self.system {
                System::Pbc => write!(f, "{feats}"),
                System::Scop => write!(f, "{} ({cutoff})", self.system),
                System::MiniZinc => write!(f, "Picat-SAT"),
                System::SavileRow => write!(f, "SavileRow ({pb_enc})"),
                _ => todo!(),
            }
        } else {
            write!(
                f,
                "{:?}{:?}{:?}{:?}{}{:?}{}{:?}{:?}{}",
                self.int_encoding,
                self.pb_encoding,
                self.con_encoding,
                self.model_config.add_consistency,
                cutoff,
                self.system,
                if self.split_eq { "Split" } else { "Eq" },
                self.model_config.propagate,
                self.model_config.scm,
                if self.model_config.equalize_ternaries {
                    "EQT"
                } else {
                    "ORIG"
                }
            )
        }
    }
}

pub(crate) fn check_enc_timer(
    enc_timeout: Option<f32>,
    enc_timer: Instant,
) -> Result<(), EncodeErr> {
    if let Some(timeout) = enc_timeout {
        if enc_timer.elapsed() > Duration::from_secs_f32(timeout) {
            return Err(EncodeErr::Timeout);
        }
    }
    Ok(())
}

fn main() {
    #[cfg(feature = "trace")]
    {
        let (tracer, _guard) = pindakaas::trace::Tracer::new();
        tracing::subscriber::set_global_default(tracer).expect("setting tracing default failed");
    }
    run(parse()).unwrap()
}

// fn read<'a, T: Deserialize<'a> + Clone>(p: &str) -> T {
//     let raw = std::fs::read_to_string(p).unwrap().clone();
//     serde_json::from_str::<T>(&raw).unwrap()
// }

impl Run {
    fn load(p: &str) -> Self {
        serde_json::from_str(&std::fs::read_to_string(p).unwrap()).unwrap()
    }
}

fn run(r: Run) -> Result<(), String> {
    match r {
        Run::Load { r } => {
            let raw = std::fs::read_to_string(r).unwrap();
            run(serde_json::from_str(&raw).unwrap())
        }
        Run::Analyze { .. } => analyze(r),
        Run::Scm { .. } => scm(r),
        Run::Slurm { .. } => crate::slurm::slurm(r),
        Run::Encode {
            instance,
            enc_timeout,
            experiment,
            stats,
            solver_timeout,
            aux_out,
            solve_seed,
            mem,
            check,
            ..
        } => {
            let mut encode_record = EncodeRecord {
                instance,
                experiment: Some(experiment.clone()),
                ..EncodeRecord::default()
            };

            let encode_record_path = write_stats(
                &encode_record,
                stats.as_ref(),
                Some(PathBuf::from("encodes")),
            );
            println!("Start {:?}", encode_record);
            write_stats(&encode_record, encode_record_path.as_ref(), None);

            let model = Model::from_file(encode_record.instance.as_ref().unwrap().lp.clone())?
                .with_config(experiment.model_config.clone());

            println!("model = {model}");
            let mut formula = Formula::new(model, solver_timeout, enc_timeout, mem);

            let enc_timer = Instant::now();
            let enc_res = formula.encode(&experiment, &mut encode_record, aux_out.clone());
            encode_record.time = Some(enc_timer.elapsed().as_secs_f32());
            let mut solve_record = match enc_res {
                Ok(cnf) => {
                    encode_record.statics = Some(StaticsRecord::from(&cnf));
                    write_stats(&encode_record, encode_record_path.as_ref(), None);
                    println!(
                        "Encoded {} in {} seconds as {}",
                        experiment,
                        encode_record.time.unwrap(),
                        encode_record.statics.unwrap_or_default()
                    );

                    if matches!(MODE, Mode::Encode | Mode::Analyze) {
                        SolveRecord {
                            check: Some(Ok(())),
                            ..SolveRecord::default()
                        }
                    } else {
                        formula.wcnf = Wcnf::from(cnf);
                        formula.solve(
                            solve_seed.unwrap_or(42),
                            encode_record.principal,
                            &experiment,
                        )
                    }
                }
                Err(e) => SolveRecord {
                    status: Status::Error(e),
                    ..SolveRecord::default()
                },
            };

            if check {
                solve_record.check = solve_record.check(&formula.model);
            }

            println!("SOLVE CALL RESULT: {solve_record}");

            write_stats(
                &(encode_record_path, &[solve_record]),
                stats.as_ref(),
                Some(PathBuf::from("solves")),
            );
            Ok(())
        }
        _ => todo!(), // Run::Solve {
                      //     path,
                      // } => {
                      //     let encode_record: EncodeRecord =
                      //         serde_json::from_str(&std::fs::read_to_string(path.clone()).unwrap()).unwrap();
                      //     let solve_records = vec![Formula::solve_cmd(
                      //         encode_record.dimacs.unwrap(),
                      //         PathBuf::from_str(&sat_cmd).unwrap(),
                      //         solver_timeout,
                      //         solve_seed.unwrap_or(42),
                      //         encode_record.principal.unwrap(),
                      //     )];
                      //     if !keep_file {
                      //         remove_file(&path).unwrap();
                      //     }
                      //     write_stats((path, solve_seed, solve_records), stats, "solve-");
                      // }
    }
}
use serde::Serialize;
fn write_stats(
    record: &impl Serialize,
    stats: Option<&PathBuf>,
    prefix: Option<PathBuf>,
) -> Option<PathBuf> {
    stats.cloned().map(|mut stats| {
        if stats.is_dir() {
            stats.push(format!("{}.json", rand_id()))
        } else {
            if let Some(prefix) = prefix {
                stats = stats
                    .parent()
                    .unwrap()
                    .to_path_buf()
                    .join(prefix)
                    .join(stats.file_name().unwrap());
            }
            stats.set_file_name(stats.clone().file_name().unwrap().to_str().unwrap())
        }
        to_writer_pretty(BufWriter::new(File::create(&stats).unwrap()), &record).unwrap();
        stats
    })
}

fn get_uniform_sampler(bounds: Range<C>, seed: Seed) -> impl FnMut() -> C {
    let q_sampler = Uniform::from(bounds);
    let mut fixed_seed = StdRng::seed_from_u64(seed);
    move || q_sampler.sample(&mut fixed_seed)
}

pub fn generate_mbssp(n: usize, m: usize, b: C, q: C, seed: Seed) -> Model {
    let mut model = Model::default();

    let mut sample = get_uniform_sampler(1..(q as C + 1), seed);
    let css = (1..=n)
        .map(|_| (1..=m).map(|_| sample()).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let int_vars: Vec<_> = (1..=m)
        .map(|j| model.new_var(&(0..=b).collect_vec(), format!("x_{j}")))
        .try_collect()
        .unwrap();

    let mut sample = get_uniform_sampler(0..(b + 1), seed);
    let solution = int_vars.iter().map(|_| sample()).collect::<Vec<_>>();

    let ks = (1..=n)
        .map(|i| {
            (1..=m)
                .map(|j| css[i - 1][j - 1] * solution[j - 1])
                .sum::<C>()
        })
        .collect::<Vec<_>>();

    css.into_iter()
        .zip(ks)
        .enumerate()
        .try_for_each(|(i, (cs, k))| {
            model.add_constraint(Lin::new(
                &int_vars
                    .iter()
                    .zip(cs)
                    .map(|(x, c)| Term::new(c, x.clone()))
                    .collect_vec(),
                Comparator::Equal,
                k,
                format!("c_{}", i + 1),
            ))
        })
        .unwrap();
    model
}

fn generate_mbkp(
    n_: usize,
    bound: C,
    m_: usize,
    q_: C,
    family: usize,
    families: usize,
    seed: usize,
    scale: Option<(f32, f32)>,
) -> Model {
    // println!("Gen {family}/{families}");
    let q_sampler = Uniform::from(1..q_ as C);
    let mut fixed_seed = StdRng::seed_from_u64(seed as u64);
    let mut sample = |_| q_sampler.sample(&mut fixed_seed);

    let (fl, fu) = scale.unwrap_or((0.0, 1.0));

    let profits: Vec<C> = (0..n_).map(&mut sample).collect();
    let weights: Vec<Vec<C>> = (0..m_)
        .map(|_| (0..n_).map(&mut sample).collect())
        .collect();

    let generate_capacity = |qs: &Vec<C>, bound: C, family: usize, families: usize| {
        let f = (family as f32) / (families as f32);
        let f = (f * (fu - fl)) + fl;
        let k = (bound as C) * ((f * (qs.iter().sum::<C>() as f32)) as C);
        // println!(
        //     "{family}/{families} = {f} * sum({}) <= {k}",
        //     qs.iter().join("+")
        // );
        k
    };

    let max_weight = weights
        .iter()
        .map(|w| generate_capacity(w, bound, family, families))
        .collect::<Vec<_>>();

    let min_profit: C = generate_capacity(&profits, bound, families - family, families);

    let (m_, weights, max_weight, profits, min_profit) =
        (bound, weights, max_weight, profits, min_profit);
    encode_bkp(m_, weights, max_weight, profits, min_profit, true)
}

fn encode_bkp(
    bound: C,
    weights: Vec<Vec<C>>,
    max_weight: Vec<C>,
    profits: Vec<C>,
    min_profit: C,
    skip_obj: bool,
) -> Model {
    let mut model = Model::default();

    assert!(max_weight.len() == weights.len());
    assert!(weights[0].len() == profits.len());

    let int_vars = (1..=weights[0].len())
        .map(|id| {
            model
                .new_var(&(0..=(bound as C)).collect::<Vec<_>>(), format!("x_{}", id))
                .unwrap()
        })
        .collect::<Vec<_>>();

    weights
        .into_iter()
        .zip(max_weight)
        .enumerate()
        .try_for_each(|(i, (w, cap))| {
            model.add_constraint(Lin {
                exp: LinExp {
                    terms: w
                        .into_iter()
                        .zip(int_vars.clone())
                        .map(|(w, x)| Term::new(w, x))
                        .collect::<Vec<_>>(),
                },
                cmp: Comparator::LessEq,
                k: cap,
                lbl: format!("w{}", i + 1),
            })
        })
        .unwrap();

    if skip_obj {
        model
            .add_constraint(Lin {
                exp: LinExp {
                    terms: profits
                        .into_iter()
                        .zip(int_vars)
                        .map(|(w, x)| Term::new(w, x))
                        .collect::<Vec<_>>(),
                },
                cmp: Comparator::GreaterEq,
                k: min_profit,
                lbl: String::from("profits"),
            })
            .unwrap();
        // Ilp::new(int_vars, [weights, vec![profits]].concat(), Obj::Satisfy)
        model
    } else {
        todo!();
        // let profits = IlpExp::new(int_vars.iter().map(Rc::clone).collect(), profits);
        // Ilp::new(int_vars, weights, Obj::Maximize(Some(profits)))
        // model
    }
}

/*
fn ilp(
    formula: &mut Formula,
    encoder: &mut LinearEncoder<PbcEncoder>,
    experiment: Experiment,
    ilp: Ilp,
    sat_cmd: Option<String>,
    mut aux_out: Option<PathBuf>,
    solve_seed: Option<usize>,
    _check: bool,
) -> (
    f32,
    Option<PathBuf>,
    Option<StaticsRecord>,
    Vec<SolveRecord>,
) {
    let enc_timer = Instant::now();

    match experiment.system {
        System::Pbc | System::PbLib => {
            let enc = formula.encode(encoder, ilp.clone(), &experiment, aux_out.clone());
            let enc_time = enc_timer.elapsed().as_secs_f32();
            let statics = formula.stats();

            let (enc, dimacs) = match enc {
                Ok(enc) => enc,
                Err(err) => {
                    return (
                        enc_time,
                        None,
                        Some(formula.stats()),
                        vec![SolveRecord {
                            status: Status::Error(err),
                            check: Some(Ok(())),
                            ..Default::default()
                        }],
                    );
                }
            };

            let last_var = *enc.values().flatten().max().unwrap();
            println!(
                "ENCODED: {} in {:?} ({:?}, {:?})",
                experiment,
                enc_time,
                formula.stats(),
                encoder.enc.pb_statics
            );

            let mut _obj_con: Option<LinVariant<_, _>> = None;
            if let Some(sat_cmd) = sat_cmd {
                let mut solve_records: Vec<SolveRecord> = vec![];
                loop {
                    let all_solutions = false;
                    if all_solutions {
                        let aux_out = aux_out.map(|mut dimacs| {
                            dimacs.set_extension("dimacs");
                            dimacs
                        });
                        let principal = enc.values().flatten().cloned().collect::<Vec<Lit>>();
                        let sols = formula.enumerate(principal, None, sat_cmd, aux_out);
                        println!("sols = {sols:?}");
                        break;
                    } else {
                        if sat_cmd != *"pbc" {
                            aux_out = aux_out.clone().map(|mut dimacs| {
                                dimacs.set_extension("dimacs");
                                dimacs
                            });
                        }

                        let mut solve_record = formula.solve(
                            sat_cmd.clone(),
                            &ilp.obj,
                            solve_seed.unwrap_or(42),
                            last_var,
                            aux_out.clone(),
                        );

                        if let Some(Err(err)) = &solve_record.check {
                            println!("CHECK FAILED: {:?}", err);
                        }

                        // TODO cost -> obj
                        solve_record.cost = ilp.obj.obj().and_then(|obj| {
                            solve_record.solution.as_ref().map(|solution| {
                                let lit_assignment = formula.assign_lits(solution);
                                let int_assignment = ilp.assign_ints(
                                    &lit_assignment,
                                    &enc,
                                    &experiment.int_encoding,
                                );

                                obj.assign(&int_assignment)
                            })
                        });

                        if let Some(solver_timeout) = formula.solver_timeout {
                            formula.solver_timeout = Some(solver_timeout - solve_record.time);
                        }

                        if solve_record.status == Status::Unsat && !solve_records.is_empty() {
                            assert!(solve_records[solve_records.len() - 1].status == Status::Sat);
                            solve_record.status = Status::Opt
                        }

                        println!(
                            "STATUS: {} (time remaining: {:?}/{:?})",
                            solve_record, formula.solver_timeout, formula.enc_timeout
                        );

                        let push_opt =
                            |solve_records: &mut Vec<SolveRecord>, solver_timeout: &Option<f32>| {
                                let opt = SolveRecord {
                                    status: Status::Opt,
                                    check: Some(Ok(())),
                                    ..Default::default()
                                };

                                println!("SOLVED: {} (time remaining: {:?})", opt, solver_timeout);

                                solve_records.push(opt);
                            };

                        solve_records.push(solve_record.clone());
                        if matches!(
                            solve_record.status,
                            Status::Unsat | Status::Opt | Status::Unknown | Status::Error(_)
                        ) {
                            break;
                        }

                        // Aggregate objective if we haven't done so already
                        const CACHE_OBJ: bool = false;

                        #[allow(unreachable_code)]
                        if CACHE_OBJ {
                            todo!("set cmp");
                            if _obj_con.is_none() {
                                if let Some(obj) = ilp.obj.obj() {
                                    let lin_exp = obj.clone().into_lin_exp(
                                        &enc,
                                        &experiment.int_encoding,
                                        &experiment.con_encoding,
                                        &vec![],
                                        &[],
                                    );

                                    let (cmp, k) = match ilp.obj {
                                        Obj::Minimize(_) => {
                                            (Comparator::LessEq, solve_record.cost.unwrap() - 1)
                                        }
                                        Obj::Maximize(_) => {
                                            (Comparator::GreaterEq, solve_record.cost.unwrap() + 1)
                                        }
                                        Obj::Satisfy => unreachable!(),
                                    };

                                    let constraint =
                                        LinearConstraint::<Lit, C>::new(lin_exp, cmp, k);
                                    match encoder.agg.aggregate(formula, &constraint) {
                                        Ok(obj_con_agg) => {
                                            _obj_con = Some(obj_con_agg);
                                        }
                                        Err(Unsatisfiable) => {
                                            push_opt(&mut solve_records, &formula.solver_timeout);
                                            break;
                                        }
                                    }
                                }
                            }

                            if let Some(ref obj_con) = _obj_con {
                                let (_, k) = match ilp.obj {
                                    Obj::Minimize(_) => {
                                        (Comparator::LessEq, solve_record.cost.unwrap() - 1)
                                    }
                                    Obj::Maximize(_) => {
                                        (Comparator::GreaterEq, solve_record.cost.unwrap() + 1)
                                    }
                                    Obj::Satisfy => unreachable!(),
                                };

                                let obj_con = match obj_con {
                                    LinVariant::Linear(lin) => {
                                        let mut new_lin = lin.clone();
                                        new_lin.set_k(k);
                                        LinVariant::Linear(new_lin)
                                    }
                                    _ => todo!(),
                                };

                                let enc_timer = Instant::now();
                                if encoder.enc.encode(formula, &obj_con) == Err(Unsatisfiable) {
                                    push_opt(&mut solve_records, &formula.solver_timeout);
                                    break;
                                }
                                let enc_time = enc_timer.elapsed().as_secs_f32();
                                println!("ENCODED: in {:?}", enc_time);
                                if enc_time < 0.0 {
                                    panic!("Encoding timeout!")
                                }

                                if let Some(enc_timeout) = formula.enc_timeout {
                                    formula.enc_timeout = Some(enc_timeout - enc_time);
                                }
                            } else {
                                break;
                            }
                        } else if let Some(obj) = ilp.obj.obj() {
                            let lin_exp = obj.clone().into_lin_exp(
                                &enc,
                                &experiment.int_encoding,
                                &experiment.con_encoding,
                                &vec![],
                                &[],
                            );

                            let (cmp, k) = match ilp.obj {
                                Obj::Minimize(_) => {
                                    (Comparator::LessEq, solve_record.cost.unwrap() - 1)
                                }
                                Obj::Maximize(_) => {
                                    (Comparator::GreaterEq, solve_record.cost.unwrap() + 1)
                                }
                                Obj::Satisfy => unreachable!(),
                            };

                            let enc_timer = Instant::now();
                            let constraint = LinearConstraint::<Lit, C>::new(lin_exp, cmp, k);
                            let res = encoder.encode(formula, &constraint);
                            let enc_time = enc_timer.elapsed().as_secs_f32();
                            println!("ENCODED: in {:?}", enc_time);
                            if let Some(enc_timeout) = formula.enc_timeout {
                                formula.enc_timeout = Some(enc_timeout - enc_time);
                                if formula.enc_timeout.unwrap() < 0.0 {
                                    panic!("Encoding timeout!")
                                }
                            }

                            if res == Err(Unsatisfiable) {
                                push_opt(&mut solve_records, &formula.solver_timeout);
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }

                (enc_time, dimacs, Some(statics), solve_records)
            } else {
                let aux_out = formula.write(aux_out, &ilp.obj);
                (enc_time, Some(aux_out), Some(formula.stats()), vec![])
            }
        }
        System::Abio => {
            #[cfg(not(debug_assertions))]
            let id = rand_id();
            #[cfg(debug_assertions)]
            let id = String::from("dev");

            let lp = std::path::PathBuf::from_str(&format!("/tmp/abio-{}.lp", id)).unwrap();
            ilp.to_file(lp.clone()).unwrap();
            let aux_out = aux_out.unwrap_or_else(|| {
                std::path::PathBuf::from_str(&format!("/tmp/abio-{}.dimacs", id)).unwrap()
            });
            let mut file = File::create(&aux_out).unwrap();

            write!(
                file,
                "{}",
                String::from_utf8(
                    Command::new("./bin/abio/main")
                        .stdin(Stdio::from(
                            Command::new("cat")
                                .arg(lp)
                                .stdout(Stdio::piped())
                                .spawn()
                                .unwrap()
                                .stdout
                                .unwrap(),
                        ))
                        .stdout(Stdio::piped())
                        .output()
                        .unwrap()
                        .stdout
                )
                .unwrap()
            )
            .unwrap();
            let enc_time = enc_timer.elapsed().as_secs_f32();

            let cnf = Cnf::from_file(&aux_out).unwrap();
            formula.merge_in(cnf).unwrap();

            (enc_time, Some(aux_out), Some(formula.stats()), vec![])
        }
    }
}
*/

fn generate_mmkp(
    k_: usize,
    n_: usize,
    m_: usize,
    q_: usize,
    family: u32,
    s_: u32,
    seed: u64,
) -> (Vec<Vec<Vec<C>>>, Vec<C>) {
    let q_sampler = Uniform::from(1..q_);
    let mut fixed_seed = StdRng::seed_from_u64(seed);
    let mut sample = || q_sampler.sample(&mut fixed_seed);

    let qsss: Vec<Vec<Vec<C>>> = (0..n_)
        .map(|_| {
            (0..m_)
                .map(|_| (0..k_).map(|_| C::try_from(sample()).unwrap()).collect())
                .collect()
        })
        .collect();

    let ks: Vec<C> = (0..k_)
        .map(|k| {
            generate_capacity(
                qsss.iter()
                    .map(|qss| qss.iter().map(|qs| qs[k]).collect())
                    .collect(),
                n_,
                family,
                s_,
            )
        })
        .collect();
    (qsss, ks)
}

fn generate_capacity(qss: Vec<Vec<C>>, n_: usize, family: u32, s_: u32) -> C {
    let (min_k, max_k) = (0..n_).fold((0 as f32, 0 as f32), |(a, b), i| {
        (
            a + *qss[i].iter().min().unwrap() as f32,
            b + *qss[i].iter().max().unwrap() as f32,
        )
    });
    let f = family as f32 / ((s_ + 1) as f32);
    (f * (max_k - min_k) + min_k) as C
}

// fn mmkp(
//     formula: &mut Formula,
//     k_: usize,
//     n_: usize,
//     m_: usize,
//     q_: usize,
//     family: u32,
//     s_: u32,
//     seed: u64,
//     experiment: Experiment,
// ) {
//     print!("result,mmkp,");
//     println!("== Experiment {:?} ==", experiment);
//     let (qsss, ks) = generate_mmkp(k_, n_, m_, q_, family, s_, seed);
//     encode_mmkp(formula, k_, n_, m_, qsss, ks, &experiment);
//     formula.solve();
// }

// fn encode_mmkp(
//     formula: &mut Formula,
//     k_: usize,
//     n_: usize,
//     m_: usize,
//     qsss: Vec<Vec<Vec<C>>>,
//     ks: Vec<C>,
//     experiment: &Experiment,
// ) {
//     let enc_timer = Instant::now();

//     let Experiment(int_encoding, pb_encoding, _, add_consistency) = experiment;
//     formula.int_vars = (0..n_).map(|_| IntVar::new(m_ as C)).collect();

//     for k in 0..k_ {
//         println!("Experiment (main) Pb {}/{}", &k + 1, k_);
//         formula
//             .add_pb(
//                 qsss.iter()
//                     .flat_map(|qss_i| {
//                         let qss_ik: Vec<C> = qss_i.iter().map(|qss_ij| qss_ij[k]).collect();
//                         match experiment {
//                             Experiment(IntEncoding::Dir, _, _, _) => qss_ik,
//                             Experiment(IntEncoding::Ord, _, _, _) => std::iter::once(0)
//                                 .chain(qss_ik.into_iter())
//                                 .tuple_windows()
//                                 .map(|(a, b)| b - a)
//                                 .collect(),
//                             Experiment(IntEncoding::Bin, _, _, _) => todo!(),
//                         }
//                     })
//                     .collect(),
//                 int_vars
//                     .iter()
//                     .flat_map(|int_var| int_var.xs.unwrap().clone())
//                     .collect::<Vec<C>>(),
//                 Comparator::LessEq,
//                 ks[k],
//                 int_vars
//                     .iter()
//                     .map(|int_var| int_var.get_constraint(&experiment.0))
//                     .collect::<Vec<Constraint<C, C>>>(),
//                 &pb_encoding,
//                 &add_consistency,
//             )
//             .unwrap();

//         if let Some(timeout) = formula.enc_timeout {
//             if enc_timer.elapsed() > Duration::from_secs(timeout) {
//                 let err = format!("ENCODING_TIMEOUT AFTER {k} main PBs");
//                 println!("{err}");
//                 panic!("{err}");
//             }
//         }
//     }

//     let avg_k: f32 = ks.iter().sum::<C>() as f32 / ks.len() as f32;
//     print!(
//         "{avg_k},{},{},{},{},",
//         experiment.0, experiment.1, experiment.2, experiment.3
//     );

//     let (stat_vars, stat_cls, stat_lits) = formula.stats();
//     let enc_time = enc_timer.elapsed().as_secs_f32();
//     print!("{stat_vars},{stat_cls},{stat_lits},{enc_time},");
// }

use rand::distributions::Alphanumeric;
use rand::{thread_rng, Rng};
fn rand_id() -> String {
    let rng = thread_rng();
    rng.sample_iter(&Alphanumeric)
        .take(7)
        .map(char::from)
        .collect::<String>()
}

fn zero_pad(i: usize, ub: usize) -> String {
    format!("{:0n$}", i, n = (ub as f32 + 1.0).log10().ceil() as usize)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::cli::*;
    use super::formula::*;
    use super::*;
    use itertools::iproduct;

    use crate::cli::{ConEncoding, ExperimentGen, IntEncoding, PbEncoding, System};

    #[test]
    fn test_results() {
        for (model, exp_res) in [
            (
                Model::from_file("instances/integration/trivial_sat.lp".into()).unwrap(),
                Status::Error(EncodeErr::Trivial(true)),
            ),
            (
                Model::from_file("instances/integration/trivial_unsat.lp".into()).unwrap(),
                Status::Error(EncodeErr::Trivial(false)),
            ),
            (
                generate_mbkp(100, 100, 100, 256, 1, 2, 42, None),
                Status::Error(EncodeErr::Timeout),
            ),
            (
                generate_mbkp(100, 100, 100, 256, 1, 2, 42, None),
                Status::Error(EncodeErr::Memory),
            ),
            (
                Model::from_file("instances/integration/le_1.lp".into()).unwrap(),
                Status::Sat,
            ),
            (
                Model::from_file("instances/integration/unsat.lp".into()).unwrap(),
                Status::Unsat,
            ),
            (
                generate_mbkp(10, 10, 50, 64, 1, 2, 42, None),
                Status::Unknown,
            ),
        ] {
            for exp in [
                Experiment::default(),
                Experiment::picat(),
                Experiment::savile_row(PbEncoding::Bdd),
                Experiment::scop(Mix::Mix(1)),
            ] {
                if matches!(
                    (&exp_res, &exp.system),
                    (
                        Status::Error(EncodeErr::Trivial(true)),
                        System::Pbc | System::Scop
                    ) | (Status::Error(EncodeErr::Timeout), System::Pbc)
                        | (
                            Status::Error(EncodeErr::Memory),
                            System::Pbc | System::MiniZinc
                        )
                ) || (exp.system != System::Pbc
                    && matches!(exp_res, Status::Sat | Status::Unsat | Status::Unknown))
                {
                    continue;
                }

                let enc_timeout = if exp_res == Status::Error(EncodeErr::Timeout) {
                    Some(3.0)
                } else {
                    Some(20.0)
                };

                let mem = if exp_res == Status::Error(EncodeErr::Memory) {
                    Some(0.1)
                } else {
                    Some(1.0)
                };

                println!("{exp} expecting {exp_res} for model:\n{model}");
                let mut enc_rec = EncodeRecord::default();
                let mut formula = Formula::new(model.clone(), Some(0.1), enc_timeout, mem);
                let actual_res = formula.encode(&exp, &mut enc_rec, None);
                let dimacs = format!(
                    "DIMACS: {}",
                    enc_rec
                        .dimacs
                        .map(|d| fs::read_to_string(d)
                            .unwrap_or_else(|_| panic!("dimacs set but doesn't exist.")))
                        .unwrap_or_default()
                );
                if let Err(e) = actual_res {
                    assert_eq!(
                        Status::Error(e.clone()),
                        exp_res,
                        "Expected {exp_res} by {exp}, but got {e}, for model:\n{model}\n{dimacs}",
                    );
                } else {
                    formula.wcnf = Wcnf::from(actual_res.unwrap());
                    let status = formula.solve(42, None, &exp).status;
                    assert_eq!(
                        status, exp_res,
                        "Expected {exp_res} by {exp}, but got {status}, for model:\n{model}\n{dimacs}"
                    );
                }
            }
        }
    }

    #[test]
    fn integration_test() {
        let name = String::from("integration");
        let analyze = Run::Analyze {
            paths: vec![format!("experiments/{name}").into()],
            check: true,
            plot: true,
            table: true,
            y_log: false,
            vbs: false,
            scatter: false,
            max_seed: None,
            save_to: None,
            fmt: "png".into(),
            filter_trivial: false,
        };
        assert!([
            Run::load("./experiments/integration/slurm.json"),
            // Run::Slurm {
            //     name,
            //     seeds: 1,
            //     build: false,
            //     enc_timeout: 3.0,
            //     solver_timeout: 3.0,
            //     grace_timeout: 1.0,
            //     mem: 2.0,
            //     nodelist: Nodelist::Local,
            //     experiments: serde_json::from_str(
            //         &std::fs::read_to_string("./solvers/integration.json").unwrap()
            //     )
            //     .unwrap(),
            //     // experiments: [
            //     //     Experiment::default(),
            //     //     Experiment::picat(),
            //     //     Experiment::savile_row(PbEncoding::Bdd),
            //     //     Experiment::scop(Mix::Mix(1)),
            //     // ],
            //     check: true,
            //     problems: vec![Problem::Pbp {
            //         path: "./instances/integration".into(),
            //         grep: None,
            //         limit: None,
            //     }]
            // },
            // Run::Load {
            //     r: PathBuf::from(format!("experiments/{name}/slurm.json"))
            // },
            analyze.clone()
        ]
        .into_iter()
        .map(run)
        .collect::<Result<Vec<_>, _>>()
        .is_ok());
    }
}
