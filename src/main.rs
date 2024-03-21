#![allow(clippy::too_many_arguments)]
#![allow(dead_code)]
use cli::PbStaticsRecord;
use core::ops::Range;
use formula::EncodeErr;
use itertools::Itertools;
use pindakaas::Cardinality;
use pindakaas::Consistency;
use pindakaas::Decomposer;
use pindakaas::LimitComp;
use pindakaas::LinearConstraint;
use pindakaas::Model;
use pindakaas::ModelConfig;
use pindakaas::Obj;
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
    cli::{parse, AddConsistency, EncodeRecord, Experiment, PbEncoding, Run, SolveRecord, System},
    formula::{Formula, Lit, Status, C},
};

use pindakaas::{
    AdderEncoder, BddEncoder, Comparator, Encoder, LadderEncoder, LinVariant, LinearAggregator,
    Result, SortedEncoder, SortedStrategy, SortingNetworkEncoder, SwcEncoder, TotalizerEncoder,
};
use rand::distributions::{Distribution, Uniform};
use rand::{rngs::StdRng, SeedableRng};
use std::time::Instant;

mod analyze;
mod scm;
mod slurm;

mod cli;
mod formula;
mod ilp;

#[derive(Default)]
enum Mode {
    #[default]
    Solve,
    Encode,
    Analyze,
}

#[derive(Default)]
pub struct PbcEncoder {
    pub pb_enc: PbEncoding,
    gt_lin_enc: TotalizerEncoder<C>,
    swc_lin_enc: SwcEncoder<C>,
    bdd_lin_enc: BddEncoder<C>,
    ladder_amo_enc: LadderEncoder,
    sn_card_enc: SortingNetworkEncoder,
    agg: LinearAggregator,
    split_eq: bool,
    pb_statics: PbStaticsRecord,
    mode: Mode,
}

const MODE: Mode = Mode::Solve;
const REMOVE_DIMACS: bool = true;

impl PbcEncoder {
    pub(crate) fn new(experiment: &Experiment, agg: LinearAggregator) -> Self {
        let add_consistency = experiment.add_consistency == AddConsistency::Aux;
        let sorted_strategy = SortedStrategy::Mixed(10);
        let propagate = if experiment.propagate {
            Consistency::Bounds
        } else {
            Consistency::None
        };

        let mut gt_lin_enc = TotalizerEncoder::default();
        gt_lin_enc.add_consistency(add_consistency);
        gt_lin_enc.add_cutoff(experiment.model_config.cutoff);
        gt_lin_enc.add_propagation(propagate.clone());
        let mut swc_lin_enc = SwcEncoder::default();
        swc_lin_enc.add_consistency(add_consistency);
        swc_lin_enc.add_cutoff(experiment.model_config.cutoff);
        swc_lin_enc.add_propagation(propagate);
        let mut bdd_lin_enc = BddEncoder::default();
        bdd_lin_enc.add_consistency(add_consistency);
        bdd_lin_enc.add_cutoff(experiment.model_config.cutoff);

        let mut sn_card_enc = SortingNetworkEncoder::default();
        sn_card_enc.sorted_encoder.set_strategy(sorted_strategy);
        sn_card_enc.sorted_encoder.add_consistency(add_consistency);

        Self {
            pb_enc: experiment.pb_encoding.clone(),
            gt_lin_enc,
            swc_lin_enc,
            bdd_lin_enc,
            sn_card_enc,
            ladder_amo_enc: LadderEncoder::default(),
            agg,
            split_eq: experiment.split_eq,
            pb_statics: PbStaticsRecord::default(),
            mode: MODE,
        }
    }
}

impl Encoder<Formula, LinVariant<Lit, C>> for PbcEncoder {
    fn encode(&mut self, db: &mut Formula, lin_variant: &LinVariant<Lit, C>) -> Result {
        if !matches!(lin_variant, LinVariant::Trivial) {
            #[cfg(feature = "trace")]
            println!("{:?}", lin_variant);
        }

        let encode = matches!(self.mode, Mode::Solve | Mode::Encode);

        match lin_variant {
            LinVariant::Linear(lin) => {
                //let s = format!("{lin_variant:?}");
                //println!("{:.180}", s);
                if lin.cmp == LimitComp::Equal {
                    self.pb_statics.lin_eqs += 1;
                } else {
                    self.pb_statics.lin_les += 1;
                }

                let lin = if lin.cmp == LimitComp::Equal && self.split_eq {
                    let mut lin_ge = LinearConstraint::<Lit, C>::from(lin.clone());
                    lin_ge.set_cmp(Comparator::GreaterEq);
                    let lin_ge = self.agg.aggregate(db, &lin_ge)?;
                    self.encode(db, &lin_ge)?;
                    let mut lin = lin.clone();
                    lin.cmp = LimitComp::LessEq;
                    lin
                } else {
                    lin.clone()
                };

                if !encode {
                    return Ok(());
                }

                if lin.len() <= 2 {
                    return self.gt_lin_enc.encode(db, &lin);
                }

                match self.pb_enc {
                    PbEncoding::Gt => self.gt_lin_enc.encode(db, &lin),
                    PbEncoding::Swc => self.swc_lin_enc.encode(db, &lin),
                    PbEncoding::Bdd => self.bdd_lin_enc.encode(db, &lin),
                    PbEncoding::Adder => AdderEncoder::default().encode(db, &lin),
                    _ => panic!(),
                }
            }
            LinVariant::Cardinality(card) => {
                if card.cmp == LimitComp::Equal {
                    self.pb_statics.card_eqs += 1;
                } else {
                    self.pb_statics.card_les += 1;
                }

                if !encode {
                    return Ok(());
                }

                self.sn_card_enc.encode(db, card)

                /*
                use pindakaas::Linear;
                // self.gt_lin_enc
                //     .encode(db, &Into::<Linear<_, _>>::into(card.clone()))

                let lin = Into::<Linear<_, _>>::into(card.clone());
                match self.pb_enc {
                    PbEncoding::Gt => self.gt_lin_enc.encode(db, &lin),
                    PbEncoding::Swc => self.swc_lin_enc.encode(db, &lin),
                    PbEncoding::Bdd => self.bdd_lin_enc.encode(db, &lin),
                    PbEncoding::Adder => AdderEncoder::default().encode(db, &lin),
                    _ => panic!(),
                }
                */
            }
            LinVariant::CardinalityOne(amo) => {
                if amo.cmp == LimitComp::Equal {
                    self.pb_statics.amo_eqs += 1;
                } else {
                    self.pb_statics.amo_les += 1;
                }

                if !encode {
                    return Ok(());
                }
                self.ladder_amo_enc.encode(db, amo)
            }
            LinVariant::Trivial => {
                self.pb_statics.trivs += 1;
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for Experiment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cutoff = match self.model_config.cutoff {
            None => "Ord".into(),
            Some(0) => "Bin".into(),
            Some(c) => format!("Hyb_{c}_"),
        };
        if self.system == System::Scop {
            return write!(f, "{:?}{}", self.system, cutoff);
        }

        write!(
            f,
            "{:?}{:?}{:?}{:?}{}{:?}{:?}{}{}{:?}",
            self.int_encoding,
            self.pb_encoding,
            self.con_encoding,
            self.add_consistency,
            cutoff,
            self.sort_same_coefficients,
            self.system,
            if self.split_eq { "Split" } else { "Eq" },
            if self.propagate { "Bounds" } else { "None" },
            self.model_config.scm
        )
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

fn run(r: Run) -> Result<(), String> {
    let mut encode_record = EncodeRecord::default();

    to_writer_pretty(BufWriter::new(File::create("./dev.json").unwrap()), &r).unwrap();

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
            int_encoding,
            pb_encoding,
            con_encoding,
            add_consistency,
            sort_same_coefficients,
            cutoff,
            system,
            split_eq,
            propagate,
            scm,
            stats,
            solver_timeout,
            sat_cmd,
            aux_out,
            solve_seed,
            ..
        } => {
            let experiment = Experiment {
                int_encoding,
                pb_encoding: pb_encoding.clone(),
                con_encoding,
                add_consistency: add_consistency.clone(),
                sort_same_coefficients,
                system,
                split_eq,
                propagate,
                model_config: ModelConfig {
                    scm,
                    cutoff,
                    decomposer: Decomposer::try_from(pb_encoding).unwrap(),
                    add_consistency: add_consistency == AddConsistency::Aux,
                    propagate: if propagate {
                        Consistency::Bounds
                    } else {
                        Consistency::None
                    },
                },
            };

            encode_record.instance = instance.clone();
            encode_record.experiment = Some(experiment.clone());

            let encode_record_path = write_stats(
                &encode_record,
                stats.clone(),
                Some(PathBuf::from("encodes")),
            );

            let mut agg = LinearAggregator::default();
            let mut sorted_enc = SortedEncoder::default();
            sorted_enc.set_strategy(SortedStrategy::Mixed(10));
            let add_consistency = experiment.add_consistency == AddConsistency::Aux;
            sorted_enc.add_consistency(add_consistency);
            agg.sort_same_coefficients(sorted_enc, experiment.sort_same_coefficients);

            // 59 * x_1=0 (=0) + 46 * x_2=7 (=322) + 132 * x_3=4 (=528) + 50 * x_4=4 (=200) + 7 * x_5=0 (=0) == 1050 !≤ 931
            let model = Model::<Lit, C>::from_file(instance.as_ref().unwrap().lp.clone())?
                .with_config(experiment.model_config.clone());

            println!("model = {model}");
            let mut formula = Formula::new(model, solver_timeout, enc_timeout);
            let enc_res = formula.encode(
                &experiment,
                &mut encode_record,
                encode_record_path.as_ref(),
                aux_out.as_ref(),
            );

            let solve_record = match enc_res {
                Ok(_) if matches!(MODE, Mode::Encode | Mode::Analyze) => SolveRecord {
                    check: Some(Ok(())),
                    ..SolveRecord::default()
                },
                Ok(cnf) => {
                    // formula.merge_in(cnf).unwrap(); // TODO unneeded?
                    formula.wcnf = Wcnf::<Lit, C>::from(cnf);
                    let mut solve_record = formula.solve(
                        sat_cmd.unwrap_or(String::from("./bin/cadical/build/cadical")),
                        &Obj::Satisfy,
                        solve_seed.unwrap_or(42),
                        encode_record.principal,
                        aux_out.clone(),
                        encode_record.dimacs.clone(),
                        REMOVE_DIMACS,
                    );

                    if experiment.system == System::Pbc {
                        solve_record.assignment = solve_record.solution.as_ref().map(|solution| {
                            formula
                                .assign(solution)
                                .unwrap()
                                .0
                                .into_iter()
                                .map(|(k, v)| (k.0, v))
                                .sorted()
                                .collect()
                        });
                    }
                    solve_record
                }
                Err(EncodeErr::Unsatisfiable) => SolveRecord {
                    status: Status::Unsat,
                    check: Some(Ok(())),
                    ..SolveRecord::default()
                },
                Err(e) => SolveRecord {
                    status: Status::Error(e),
                    ..SolveRecord::default()
                },
            };

            if REMOVE_DIMACS {
                if let Some(dimacs) = encode_record.dimacs.as_ref() {
                    if dimacs.exists() {
                        remove_file(dimacs).unwrap();
                    }
                }
            }

            write_stats(
                &(encode_record_path, &[solve_record]),
                stats,
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
    stats: Option<PathBuf>,
    prefix: Option<PathBuf>,
) -> Option<PathBuf> {
    stats.map(|mut stats| {
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

fn get_uniform_sampler(bounds: Range<C>, seed: u64) -> impl FnMut() -> C {
    let q_sampler = Uniform::from(bounds);
    let mut fixed_seed = StdRng::seed_from_u64(seed);
    move || q_sampler.sample(&mut fixed_seed)
}

fn generate_mbkp(
    n_: usize,
    bound: usize,
    m_: usize,
    q_: usize,
    family: u32,
    s_: u32,
    seed: u64,
) -> (usize, Vec<Vec<C>>, Vec<C>, Vec<C>, C) {
    let q_sampler = Uniform::from(1..q_ as C);
    let mut fixed_seed = StdRng::seed_from_u64(seed);
    let mut sample = |_| q_sampler.sample(&mut fixed_seed);

    let profits: Vec<C> = (0..n_).map(&mut sample).collect();
    let weights: Vec<Vec<C>> = (0..m_)
        .map(|_| (0..n_).map(&mut sample).collect())
        .collect();

    const FL: f32 = 0.2;
    const FU: f32 = 0.8;

    let generate_capacity = |qs: &Vec<C>, bound: usize, family: u32, s_: u32| {
        let family = family as f32;
        let f = family as f32 / ((s_ + 1) as f32);
        let f = (f * (FU - FL)) + FL;
        assert!(FL <= f && f <= FU);
        (bound as C) * ((f * (qs.iter().sum::<C>() as f32)) as C)
    };

    let max_weight = weights
        .iter()
        .map(|w| generate_capacity(w, bound, family, s_))
        .collect::<Vec<_>>();

    let min_profit: C = generate_capacity(&profits, bound, s_ - family, s_);

    (bound, weights, max_weight, profits, min_profit)
}

fn encode_bkp(
    bound: usize,
    weights: Vec<Vec<C>>,
    max_weight: Vec<C>,
    profits: Vec<C>,
    min_profit: C,
    skip_obj: bool,
) -> Model<Lit, C> {
    let mut model = Model::default();

    assert!(max_weight.len() == weights.len());
    assert!(weights[0].len() == profits.len());

    let int_vars = (1..=weights[0].len())
        .map(|id| {
            model
                .var(
                    &(0..=(bound as C)).collect::<Vec<_>>(),
                    Some(format!("x_{}", id)),
                )
                .unwrap()
        })
        .collect::<Vec<_>>();

    weights
        .into_iter()
        .zip(max_weight)
        .enumerate()
        .try_for_each(|(i, (w, cap))| {
            model.con(
                &w.into_iter().zip(int_vars.clone()).collect::<Vec<_>>(),
                Comparator::LessEq,
                cap,
                Some(format!("w{i}")),
            )
        })
        .unwrap();

    if skip_obj {
        model
            .con(
                &profits.into_iter().zip(int_vars).collect::<Vec<_>>(),
                Comparator::GreaterEq,
                min_profit,
                Some(String::from("profits")),
            )
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

#[cfg(test)]
mod tests {
    use super::cli::*;
    use super::formula::*;
    use super::*;
    use itertools::iproduct;
    use pindakaas::Format;
    use pindakaas::Scm;

    fn get_experiments() -> Vec<Experiment> {
        SYSTEMS
            .into_iter()
            .flat_map(|system| {
                iproduct!(
                    system.int_encodings(),
                    system.pb_encodings(),
                    system.con_encodings(),
                    system.add_consistencies(),
                    system.cutoffs(),
                    system.split_eqs(),
                    system.propagates(),
                    [system],
                    [Scm::Add, Scm::Rca, Scm::Pow, Scm::Dnf]
                )
            })
            .into_iter()
            .map(
                |(
                    int_encoding,
                    pb_encoding,
                    con_encoding,
                    add_consistency,
                    &cutoff,
                    split_eq,
                    propagate,
                    system,
                    scm,
                )| {
                    Experiment::new(
                        int_encoding.clone(),
                        pb_encoding.clone(),
                        con_encoding.clone(),
                        system.clone(),
                        add_consistency.clone(),
                        0,
                        split_eq.clone(),
                        propagate.clone(),
                        cutoff.clone(),
                        scm.clone(),
                    )
                },
            )
            .collect::<Vec<_>>()
    }

    #[test]
    fn unary_constraint_test() {
        let lp = r"
Subject To
c0: + 2 x1 <= 6
Bounds
0 <= x1 <= 5
End
";
        test_model(lp, None, &get_experiments());
    }
    // (x):B ∈ 0,1,2,3 [2] + 0 = (z):B ∈ -4,-3 [3]
    #[test]
    fn test_int_tmp() {
        let lp = r"
Subject To
c0: x1 - x2 = 0
Doms
  x1 in 0,1,2,3
  x2 in -4,-3
End
";
        test_model(
            lp,
            None,
            &[Experiment {
                pb_encoding: PbEncoding::Gt,
                system: System::Pbc,
                int_encoding: IntEncoding::Ord,
                con_encoding: ConEncoding::Include,
                add_consistency: AddConsistency::Skip,
                model_config: ModelConfig {
                    scm: Scm::Add,
                    cutoff: Some(0),
                    decomposer: Decomposer::Gt,
                    add_consistency: false,
                    propagate: Consistency::None,
                },
                ..Experiment::default()
            }],
        );
    }

    #[test]
    fn int_lin_le_1_test() {
        let lp = r"
Subject To
c0: + 2 x1 + 3 x2 + 5 x3 <= 6
Bounds
0 <= x1 <= 2
0 <= x2 <= 2
0 <= x3 <= 2
End
";
        test_model(lp, None, &get_experiments());
    }

    // #[test]
    // fn bkp_test() {
    //     test_model(
    //         encode_bkp(1, vec![vec![4, 6, 7]], vec![10], vec![1, 2, 3], 3, true),
    //         Some(vec![vec![0, 0, 1], vec![1, 1, 0]]),
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn bkp_2_test() {
    //     test_ilp(
    //         encode_bkp(3, vec![vec![9, 5, 5]], vec![33], vec![5, 1, 11], 20, true),
    //         None,
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn gen_bkp_1_test() {
    //     let (m_, weights, max_weight, profits, min_profit) =
    //         generate_mbkp(1, 2, 1, 12, 75, 100, 42);
    //     test_ilp(
    //         encode_bkp(m_, weights, max_weight, profits, min_profit, true),
    //         None,
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn gen_bkp_2_test() {
    //     let (m_, weights, max_weight, profits, min_profit) = generate_mbkp(3, 2, 1, 6, 75, 100, 42);
    //     test_ilp(
    //         encode_bkp(m_, weights, max_weight, profits, min_profit, true),
    //         None,
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn gen_bkp_3_test() {
    //     let (m_, weights, max_weight, profits, min_profit) = generate_bkp(8, 5, 12, 75, 100, 42);
    //     test_ilp(
    //         encode_bkp(m_, weights, max_weight, profits, min_profit, SYSTEM),
    //         None,
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn medium_ilp_1_test() {
    //     let dom = HashSet::from_iter(0..=3);
    //     let int_vars = (1..=3)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         vec![2, 2, 2],
    //         Comparator::LessEq,
    //         4,
    //         None,
    //     )];
    //     test_ilp(
    //         Ilp::new(int_vars, ils, Obj::Satisfy),
    //         None,
    //         get_experiments(),
    //     );
    // }

    // // #[test]
    // fn small_ilp_test() {
    //     // TODO
    //     let dom = HashSet::from_iter(0..=2);
    //     let int_vars = vec![
    //         Rc::new(IntVar::new(1, dom.clone())),
    //         Rc::new(IntVar::new(2, dom.clone())),
    //         Rc::new(IntVar::new(3, dom.clone())),
    //     ];
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         vec![1, 2, 2],
    //         Comparator::LessEq,
    //         2,
    //         None,
    //     )];
    //     test_ilp(
    //         Ilp::new(int_vars, ils, Obj::Satisfy),
    //         None,
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn medium_ilp_2_test() {
    //     let dom = HashSet::from_iter(0..=2);
    //     let int_vars = (1..=3)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![
    //         Il::new(
    //             int_vars.iter().map(Rc::clone).collect(),
    //             vec![3, 3, 4],
    //             Comparator::LessEq,
    //             14,
    //             None,
    //         ),
    //         Il::new(
    //             int_vars.iter().map(Rc::clone).collect(),
    //             vec![3, 1, 3],
    //             Comparator::GreaterEq,
    //             2,
    //             None,
    //         ),
    //     ];
    //     test_ilp(
    //         Ilp::new(int_vars, ils, Obj::Satisfy),
    //         None,
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn medium_ilp_3_test() {
    //     let dom = HashSet::from_iter(0..=5);
    //     let int_vars = (1..=3)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         vec![3, 2, 4],
    //         Comparator::LessEq,
    //         22,
    //         None,
    //     )];
    //     let ilp = Ilp::new(int_vars, ils, Obj::Satisfy);
    //     test_ilp(
    //         ilp,
    //         Some(vec![
    //             vec![0, 0, 0],
    //             vec![0, 0, 1],
    //             vec![0, 0, 2],
    //             vec![0, 0, 3],
    //             vec![0, 0, 4],
    //             vec![0, 0, 5],
    //             vec![0, 1, 0],
    //             vec![0, 1, 1],
    //             vec![0, 1, 2],
    //             vec![0, 1, 3],
    //             vec![0, 1, 4],
    //             vec![0, 1, 5],
    //             vec![0, 2, 0],
    //             vec![0, 2, 1],
    //             vec![0, 2, 2],
    //             vec![0, 2, 3],
    //             vec![0, 2, 4],
    //             vec![0, 3, 0],
    //             vec![0, 3, 1],
    //             vec![0, 3, 2],
    //             vec![0, 3, 3],
    //             vec![0, 3, 4],
    //             vec![0, 4, 0],
    //             vec![0, 4, 1],
    //             vec![0, 4, 2],
    //             vec![0, 4, 3],
    //             vec![0, 5, 0],
    //             vec![0, 5, 1],
    //             vec![0, 5, 2],
    //             vec![0, 5, 3],
    //             vec![1, 0, 0],
    //             vec![1, 0, 1],
    //             vec![1, 0, 2],
    //             vec![1, 0, 3],
    //             vec![1, 0, 4],
    //             vec![1, 1, 0],
    //             vec![1, 1, 1],
    //             vec![1, 1, 2],
    //             vec![1, 1, 3],
    //             vec![1, 1, 4],
    //             vec![1, 2, 0],
    //             vec![1, 2, 1],
    //             vec![1, 2, 2],
    //             vec![1, 2, 3],
    //             vec![1, 3, 0],
    //             vec![1, 3, 1],
    //             vec![1, 3, 2],
    //             vec![1, 3, 3],
    //             vec![1, 4, 0],
    //             vec![1, 4, 1],
    //             vec![1, 4, 2],
    //             vec![1, 5, 0],
    //             vec![1, 5, 1],
    //             vec![1, 5, 2],
    //             vec![2, 0, 0],
    //             vec![2, 0, 1],
    //             vec![2, 0, 2],
    //             vec![2, 0, 3],
    //             vec![2, 0, 4],
    //             vec![2, 1, 0],
    //             vec![2, 1, 1],
    //             vec![2, 1, 2],
    //             vec![2, 1, 3],
    //             vec![2, 2, 0],
    //             vec![2, 2, 1],
    //             vec![2, 2, 2],
    //             vec![2, 2, 3],
    //             vec![2, 3, 0],
    //             vec![2, 3, 1],
    //             vec![2, 3, 2],
    //             vec![2, 4, 0],
    //             vec![2, 4, 1],
    //             vec![2, 4, 2],
    //             vec![2, 5, 0],
    //             vec![2, 5, 1],
    //             vec![3, 0, 0],
    //             vec![3, 0, 1],
    //             vec![3, 0, 2],
    //             vec![3, 0, 3],
    //             vec![3, 1, 0],
    //             vec![3, 1, 1],
    //             vec![3, 1, 2],
    //             vec![3, 2, 0],
    //             vec![3, 2, 1],
    //             vec![3, 2, 2],
    //             vec![3, 3, 0],
    //             vec![3, 3, 1],
    //             vec![3, 4, 0],
    //             vec![3, 4, 1],
    //             vec![3, 5, 0],
    //             vec![4, 0, 0],
    //             vec![4, 0, 1],
    //             vec![4, 0, 2],
    //             vec![4, 1, 0],
    //             vec![4, 1, 1],
    //             vec![4, 1, 2],
    //             vec![4, 2, 0],
    //             vec![4, 2, 1],
    //             vec![4, 3, 0],
    //             vec![4, 3, 1],
    //             vec![4, 4, 0],
    //             vec![4, 5, 0],
    //             vec![5, 0, 0],
    //             vec![5, 0, 1],
    //             vec![5, 1, 0],
    //             vec![5, 1, 1],
    //             vec![5, 2, 0],
    //             vec![5, 3, 0],
    //         ]),
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn ilp_leq_1_test() {
    //     let dom = HashSet::from_iter(0..=2);
    //     let int_vars = (1..=1)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         vec![6],
    //         Comparator::LessEq,
    //         8,
    //         None,
    //     )];
    //     let ilp = Ilp::new(int_vars, ils, Obj::Satisfy);
    //     test_ilp(ilp, Some(vec![vec![0], vec![1]]), get_experiments());
    // }

    // TODO needs Card constraint
    // #[test]
    // fn ilp_leq_2_test() {
    //     let mut ilp = Ilp::new(vec![6]);
    //     ilp.ils = vec![Il {
    //         int_vars: ilp.int_vars.iter().map(Rc::clone).collect(),
    //         coefs: vec![1],
    //         cmp: Comparator::LessEq,
    //         k: 5,
    //     }];
    //     test_ilp(
    //         ilp,
    //         Some(vec![vec![0], vec![1], vec![2], vec![3], vec![4], vec![5]]),
    //         get_experiments(),
    //     );
    // }

    // #[test]
    // fn ilp_card1_test() {
    //     let dom = HashSet::from_iter(0..=1);
    //     let int_vars = (1..=3)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         vec![-1, 1, 1],
    //         Comparator::GreaterEq,
    //         1,
    //         None,
    //     )];
    //     let ilp = Ilp::new(int_vars, ils, Obj::Satisfy);
    //     test_ilp(ilp, None, get_experiments());
    // }

    // #[test]
    // fn ilp_geq_1_test() {
    //     let dom = HashSet::from_iter(0..=2);
    //     let int_vars = (1..=1)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         vec![6],
    //         Comparator::GreaterEq,
    //         2,
    //         None,
    //     )];
    //     let ilp = Ilp::new(int_vars, ils, Obj::Satisfy);
    //     test_ilp(ilp, Some(vec![vec![1], vec![2]]), get_experiments());
    // }

    // #[test]
    // fn ilp_geq_2_test() {
    //     let dom = HashSet::from_iter(0..=5);
    //     let int_vars = (1..=1)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         vec![1],
    //         Comparator::GreaterEq,
    //         4,
    //         None,
    //     )];
    //     let ilp = Ilp::new(int_vars, ils, Obj::Satisfy);
    //     test_ilp(ilp, Some(vec![vec![4], vec![5]]), get_experiments());
    // }

    //    //#[test]
    //    fn ilp_lin_4() {
    //        let ilp = Ilp::from_file(PathBuf::from("./instances/toy/lin_4.lp")).unwrap();
    //        test_ilp(ilp, None, get_experiments());
    //    }

    //    //#[test]
    //    fn ilp_geq_reg_2_test() {
    //        let ilp = Ilp::from_file(PathBuf::from("./instances/toy/lin_geq_reg.lp")).unwrap();
    //        test_ilp(ilp, None, get_experiments());
    //    }

    // #[test]
    // fn ilp_geq_reg_1_test() {
    //     // +9*x1 in 0..15 +53*x2 in 0..15 +24*x3 in 0..15 +53*x4 in 0..15 +3*x5 in 0..15 +36*x6 in 0..15 +16*x7 in 0..15 +56*x8 in 0..15 +35*x9 in 0..15 +38*x10 in 0..15 +8*x11 in 0..15 +16*x12 in 0..15 +12*x13 in 0..15 +37*x14 in 0..15 +21*x15 in 0..15 >= 2835
    //     let dom = HashSet::from_iter(0..=5);
    //     let coefs = vec![9, 53, 24, 53, 3, 36, 16, 56, 35, 38, 8, 16, 12, 37, 21];
    //     let int_vars = (1..=coefs.len())
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![Il::new(
    //         int_vars.iter().map(Rc::clone).collect(),
    //         // vec![9,53,24],
    //         coefs,
    //         Comparator::GreaterEq,
    //         2835,
    //         // 75,
    //     )];
    //     let ilp = Ilp::new(int_vars, ils, Obj::Satisfy);
    //     test_ilp(ilp, None, get_experiments());
    // }

    // #[test]
    // fn ilp_lin_3() {
    //     let ilp = Ilp::from_file(PathBuf::from("./instances/toy/lin_3.lp"));
    //     test_ilp(ilp, None, get_experiments());
    // }

    // #[test]
    // fn var_int_test() {
    //     let m = 5;
    //     let dom = HashSet::from_iter(0..=m);
    //     let expected: Vec<Vec<Lit>> = (0..=m).map(|i| vec![i]).collect();
    //     let int_vars = (1..=1)
    //         .map(|id| Rc::new(IntVar::new(id, dom.clone())))
    //         .collect::<Vec<_>>();
    //     let ils = vec![];
    //     let ilp = Ilp::new(int_vars, ils, Obj::Satisfy);
    //     test_ilp(ilp, Some(expected), get_experiments());
    // }

    fn test_model(lp: &str, _expected: Option<Vec<Vec<Lit>>>, experiments: &[Experiment]) {
        for experiment in experiments {
            let model = Model::<Lit, C>::from_string(lp.into(), Format::Lp)
                .unwrap()
                .with_config(experiment.model_config.clone());
            println!("model =\n{model}");
            println!("{}", model.to_text(Format::Lp));

            let solver_timeout = Some(60.0);
            let enc_timeout = Some(10.0);

            let aux_out = PathBuf::from(format!("/tmp/test_{}", rand_id()));
            let mut formula = Formula::new(model, solver_timeout, enc_timeout);

            // TODO None => experiment
            let cnf = formula
                .encode(&experiment, &mut EncodeRecord::default(), None, None)
                .unwrap();

            formula.merge_in(cnf).unwrap();

            // let sat_cmd = String::from(if is_pblib { "./bin/cadical/build/cadical"} else { "pbc" });
            let sat_cmd = String::from("./bin/cadical/build/cadical");

            if matches!(experiment.system, System::Pbc) {
                let lit_assignments = formula.enumerate(Some(1000), sat_cmd, Some(aux_out));

                let assignments = lit_assignments
                    .into_iter()
                    .flat_map(|lit_assignment| formula.assign(&lit_assignment))
                    .collect::<Vec<_>>();
                let check = formula.model.check_assignments(&assignments, None);
                assert!(check.is_ok(), "{}", check.unwrap_err().iter().join("\n"));
            }
        }
    }

    // fn test_ilp(ilp: Ilp, expected: Option<Vec<Vec<Lit>>>, experiments: Vec<Experiment>) {
    //     experiments.into_iter().for_each(|experiment| {
    //         let solver_timeout = Some(60.0);
    //         let enc_timeout = Some(10.0);

    //         match experiment.system {
    //             System::MiniZinc | System::Abio | System::Scop => todo!(),
    //             System::SavileRow | System::SavileRowBasic => {
    //                 let formula = Formula::new(solver_timeout, enc_timeout);
    //                 let (_, _, _, _, int_assignment) = formula.essence(
    //                     &ilp,
    //                     &experiment,
    //                     Some(PathBuf::from_str("./bin/cadical/build/cadical").unwrap()),
    //                     None,
    //                 );
    //                 ilp.check(&int_assignment.as_ref().unwrap()).unwrap();
    //                 (
    //                     experiment,
    //                     vec![int_assignment.unwrap().into_values().collect::<Vec<_>>()],
    //                 )
    //             }
    //             System::Pbc | System::PbLib => {
    //                 let is_pblib = experiment.system == System::PbLib;
    //                 let mut formula = Formula::new(solver_timeout, enc_timeout);
    //                 let agg = LinearAggregator::default();
    //                 let mut encoder =
    //                     LinearEncoder::new(PbcEncoder::new(&experiment, agg.clone()), agg);

    //                 let aux_out = PathBuf::from(format!("/tmp/test_{}", rand_id()));

    //                 let mut lp = aux_out.clone();
    //                 lp.set_extension("lp");
    //                 ilp.to_file(lp.clone()).unwrap();
    //                 let mut model = Model::<Lit, Val>::from_file(lp).unwrap();

    //                 let mut cnf = Cnf::new(0);
    //                 model.encode(&mut cnf, None).unwrap();
    //                 let enc = (1..=cnf.literals() as Lit).collect();
    //                 formula.merge_in(cnf).unwrap();

    //                 // let sat_cmd = String::from(if is_pblib { "./bin/cadical/build/cadical"} else { "pbc" });
    //                 let sat_cmd = String::from("./bin/cadical/build/cadical");

    //                 let lit_assignments =
    //                     formula.enumerate(enc, Some(1000), sat_cmd, Some(aux_out));

    //                 let assignments = lit_assignments
    //                     .into_iter()
    //                     .flat_map(|lit_assignment| model.assign(&lit_assignment))
    //                     .collect::<Vec<_>>();

    //                 (experiment, vec![])

    //                 //                     (
    //                 //                         experiment,
    //                 //                         lit_assignments
    //                 //                             .into_iter()
    //                 //                             .flat_map(|lit_assignment| model.assign(&lit_assignment))
    //                 //                             .collect(),
    //                 //                     )

    //                 // for model in &models {
    //                 //     // formula.check(&Status::Sat, Some(&model), &ilp, &enc, &experiment.int_encoding).expect(&format!("Model check failed on experiment {experiment:?}:"));
    //                 // }

    //                 // let mut assignments = models
    //                 //     .iter()
    //                 //     .map(|solution| {
    //                 //         let lit_assignment = formula.assign_lits(&solution);
    //                 //         ilp.assign_ints(&lit_assignment, &enc, &experiment.int_encoding)
    //                 //     })
    //                 //     .map(|a| {
    //                 //         // blegh
    //                 //         let mut aaa: Vec<Rc<IntVar>> = a.keys().map(|id| ilp.get_int_var(*id)).collect();
    //                 //         aaa.sort_by(|a, b| a.get_id().cmp(&b.get_id()));
    //                 //         aaa.into_iter().map(|k| a[&k.get_id()]).collect()
    //                 //     })
    //                 //     .collect::<Vec<Vec<Val>>>();

    //                 // assignments.sort();
    //                 // assignments.dedup();

    //                 // if let Some(expected) = &expected {
    //                 //     assert_eq!(
    //                 //         assignments, *expected,
    //                 //         "ILP assignment (left) was not as expected (right) for experiment {:?} for {ilp}",
    //                 //         experiment
    //                 //     );
    //                 // }
    //                 // (experiment, assignments)
    //             }
    //         };
    //     });
    // .tuple_windows()
    // .for_each(|((exp_a, a), (exp_b, b))| {
    //     if matches!((&exp_a.system, &exp_b.system), (&System::Pbc, &System::Pbc)) {
    //         assert_eq!(
    //             a, b,
    //             "Found unequal assignments for experiments {exp_a:?} and {exp_b:?} for {ilp}"
    //             )
    //     }
    // });
    // }

    use crate::cli::{AddConsistency, ConEncoding, ExperimentGen, IntEncoding, PbEncoding, System};

    #[test]
    fn integration_test() {
        let name = String::from("integration");
        assert!([
            Run::Slurm {
                name: name.clone(),
                build: false,
                seeds: 1, // TODO test
                enc_timeout: 10.0,
                solver_timeout: 10.0,
                grace_timeout: 60.0,
                nodelist: Nodelist::Local,
                experiments: vec![
                    /*
                    ExperimentGen {
                        int_encodings: vec![IntEncoding::Dir],
                        pb_encodings: vec![PbEncoding::Bdd],
                        con_encodings: vec![ConEncoding::Include],
                        add_consistencies: vec![AddConsistency::Skip],
                        cutoffs: vec![Some(0)],
                        sort_same_coefficientss: vec![0],
                        split_eqs: vec![false],
                        systems: vec![System::Scop],
                        propagates: vec![true],
                        scms: vec![0]
                    },
                    ExperimentGen {
                        int_encodings: vec![IntEncoding::Dir],
                        pb_encodings: vec![PbEncoding::Gt],
                        con_encodings: vec![ConEncoding::Include],
                        add_consistencies: vec![AddConsistency::Skip],
                        cutoffs: vec![Some(0)],
                        sort_same_coefficientss: vec![0],
                        split_eqs: vec![false],
                        systems: vec![System::SavileRow],
                        propagates: vec![true],
                        scms: vec![0]
                    },
                    */
                    ExperimentGen {
                        int_encodings: vec![IntEncoding::Ord],
                        pb_encodings: vec![PbEncoding::Gt, PbEncoding::Adder],
                        con_encodings: vec![ConEncoding::Include],
                        add_consistencies: vec![AddConsistency::Skip],
                        cutoffs: vec![None],
                        sort_same_coefficientss: vec![0],
                        split_eqs: vec![false],
                        systems: vec![
                            System::Pbc,
                            System::SavileRow,
                            System::MiniZinc,
                            System::Scop
                        ],
                        propagates: vec![true],
                        scms: vec![0],
                        skip: false
                    }
                ],
                check: true,
                sat_cmd: Some(String::from("./bin/cadical/build/cadical")),
                problems: vec![
                    Problem::Mbkp {
                        n_: 3,
                        bound: 3,
                        m_: 2,
                        q_: 12,
                        family: 1,
                        s_: 5,
                        seed: 1,
                        skip_obj: true,
                    },
                    Problem::Pbp {
                        path: "./instances/integration".into(),
                        limit: None,
                        grep: None
                    }
                ],
            },
            Run::Analyze {
                paths: vec![format!("experiments/{name}").into()],
                check: true,
                plot: true,
                y_log: false,
                vbs: false,
                scatter: false,
                max_seed: None,
                save_to: None,
                fmt: "png".into(),
            }
        ]
        .into_iter()
        .map(run)
        .collect::<Result<Vec<_>, _>>()
        .is_ok());
    }

    #[test]
    fn model_test() {
        use super::*;
        use pindakaas::{Cnf, Model};
        // let mut model = Model::<C, C>::default();
        // let x1 = model.new_var(&[0, 2], true, Some(String::from("x1")));
        // let x2 = model.new_var(&[0, 3], true, Some(String::from("x2")));
        // let x3 = model.new_var(&[0, 5], true, Some(String::from("x3")));
        // let k = 6;
        // model
        //     .add_constraint(Lin::new(
        //         &[Term::from(x1), Term::from(x2), Term::from(x3)],
        //         Comparator::LessEq,
        //         k,
        //         Some("A test constraint".to_string()),
        //     ))
        //     .unwrap();

        let lp = r"
Subject To
c0: + 2 x1 + 3 x2 + 5 x3 <= 6
Binary
x1
x2
x3
End
";
        let mut model = Model::<Lit, C>::from_string(lp.into(), Format::Lp).unwrap();

        let mut cnf = Cnf::new(0);
        model.propagate(&Consistency::Bounds).unwrap();
        model.encode(&mut cnf).unwrap();
    }
}
