#![allow(unused_variables, unreachable_code)]
use crate::cli::PbStaticsRecord;
use crate::cli::StaticsRecord;
use crate::formula::EncodeErr;
use crate::formula::C;
use pindakaas::Assignment;
use pindakaas::CheckError;
use pindakaas::IntVarId;
use pindakaas::Model;
use pindakaas::ModelConfig;
use pindakaas::Obj;
use pindakaas::Scm;
use tabled::locator::ByColumnName;
use tabled::Disable;
use tabled::{Table, Tabled};

use crate::cli::System;
use crate::formula::Lit;
pub use crate::{
    cli::{
        AddConsistency, ConEncoding, EncodeRecord, Experiment, Instance, IntEncoding, PbEncoding,
        Problem, Run, SolveRecord,
    },
    formula::Status,
};
use std::collections::hash_map::Entry;
use std::path::PathBuf;

// use itertools::MinMaxResult;
use itertools::{multiunzip, Itertools};

use serde::Serialize;
use serde_json::{json, to_writer_pretty};
use std::collections::{HashMap, HashSet};

use std::fs::File;
use std::io::BufWriter;
use std::process::Command;

const PYTHON: &str = "python";
const MKPLOT: &str = "./bin/mkplot/mkplot.py";

const TEX: bool = true;

#[derive(Debug)]
struct Acc {
    count: u64,
    vars: u64,
    cls: u64,
    lits: u64,
    enc_time: f32,
    solve_time: f32,
}

impl Acc {
    pub fn new() -> Self {
        Self {
            count: 0,
            vars: 0,
            cls: 0,
            lits: 0,
            enc_time: 0 as f32,
            solve_time: 0 as f32,
        }
    }
}

fn parse_option(opt: String) -> Option<C> {
    if opt == "None" {
        None
    } else {
        Some(opt[5..(opt.len() - 1)].parse().unwrap())
    }
}

use std::fs;

/// PAR*Timeout penalty when calculating average solve time
const PAR: f32 = 2.0;
const MAG: i32 = 3;

type ExperimentSolveRecords =
    HashMap<(Problem, Option<usize>), (EncodeRecord, HashMap<Option<usize>, Vec<SolveRecord>>)>;

pub fn analyze(run: Run) -> Result<(), String> {
    if let Run::Analyze {
        paths,
        check,
        y_log,
        plot,
        save_to,
        fmt,
        scatter,
        vbs: _,
        ..
    } = run
    {
        let runs = paths
            .into_iter()
            .map(|path| {
                (
                    path.clone(),
                    serde_json::from_str(
                        &fs::read_to_string(if path.is_dir() {
                            path.join("slurm.json")
                        } else {
                            path.clone()
                        })
                        .unwrap(),
                    )
                    .unwrap(),
                )
            })
            .collect::<Vec<(_, Run)>>();

        if let Run::Slurm {
            name,
            enc_timeout,
            solver_timeout,
            problems,
            ..
        } = &runs.first().unwrap().1
        {
            let get_key = |run: &Run, path: &PathBuf| -> (String, usize) {
                if let Run::Slurm { name, .. } = run {
                    (
                        name.clone(),
                        path.file_stem().unwrap().to_str().unwrap().parse().unwrap(),
                    )
                } else {
                    unreachable!()
                }
            };

            let filter_triv_unsat = name.contains("scm") || name.contains("pbc-mbkp");

            // Read Runs
            let mut data = runs
                .iter()
                .flat_map(|(path, run)| {
                    fs::read_dir(path.join("runs"))
                        .unwrap()
                        .map(Result::unwrap)
                        .flat_map(move |path| {
                            let key = get_key(run, &path.path());
                            let enc_rec = if let Run::Encode { .. } = serde_json::from_str::<Run>(
                                &fs::read_to_string(path.path()).unwrap(),
                            )
                            .unwrap()
                            {
                                let encode_record_path = path
                                    .path()
                                    .parent()
                                    .unwrap()
                                    .parent()
                                    .unwrap()
                                    .join("stats/encodes")
                                    .join(path.path().file_name().unwrap());
                                if !encode_record_path.exists() {
                                    return None;
                                }
                                let encode_record = serde_json::from_str::<EncodeRecord>(
                                    &fs::read_to_string(&encode_record_path).unwrap(),
                                )
                                .unwrap();

                                if encode_record.time.is_none() {
                                    let output_path = path
                                        .path()
                                        .parent()
                                        .unwrap()
                                        .parent()
                                        .unwrap()
                                        .join("output")
                                        .join(format!("{}_{}.out", key.0, key.1));

                                    let err = match fs::read_to_string(output_path) {
                                        Err(e) => EncodeErr::Error(e.to_string()),
                                        Ok(output) => {
                                            if output.contains("oom-kill event") {
                                                EncodeErr::Memory
                                            } else if output.contains("DUE TO TIME LIMIT")
                                                || output.contains("Savile Row timed out.")
                                            {
                                                EncodeErr::Timeout
                                            } else {
                                                println!(
                                                    "UNEXPECTED OUTPUT for run {}:\n{}",
                                                    path.path().display(),
                                                    output
                                                );
                                                EncodeErr::Error(output)
                                            }
                                        }
                                    };

                                    (
                                        encode_record,
                                        vec![vec![SolveRecord {
                                            status: Status::Error(err),
                                            ..SolveRecord::default()
                                        }]],
                                    )
                                } else {
                                    (encode_record, Vec::default())
                                }
                            } else {
                                todo!()
                            };

                            // Filter out old binary experiments
                            if let Run::Slurm { name, .. } = run {
                                if name == "pbc-mbkp"
                                    && matches!(
                                        enc_rec.0.experiment.as_ref().unwrap(),
                                        Experiment {
                                            model_config: ModelConfig {
                                                cutoff: Some(0),
                                                ..
                                            },
                                            ..
                                        }
                                    )
                                {
                                    return None;
                                }
                            }

                            // Filter out + prop for Bdd
                            if name == "pbc-mbssp"
                                && matches!(
                                    enc_rec.0.experiment.as_ref().unwrap(),
                                    Experiment {
                                        pb_encoding: PbEncoding::Bdd,
                                        propagate: true,
                                        split_eq: false,
                                        model_config: ModelConfig { cutoff: None, .. },
                                        ..
                                    }
                                )
                            {
                                return None;
                            }

                            Some((key, enc_rec))
                        })
                })
                .collect::<HashMap<(String, usize), (EncodeRecord, Vec<Vec<SolveRecord>>)>>();

            // Read EncodeRecords
            /*
            let mut data = paths
                .iter()
                .flat_map(|path| {
                    fs::read_dir(path.join("stats/encodes"))
                        .unwrap()
                        .map(Result::unwrap)
                        .map(|path| {
                            (
                                get_key(&path.path()),
                                (
                                    serde_json::from_str::<EncodeRecord>(
                                        &fs::read_to_string(path.path()).unwrap(),
                                    )
                                    .unwrap(),
                                    Vec::default(),
                                ),
                            )
                        })
                })
                .collect::<HashMap<usize, (EncodeRecord, Vec<Vec<SolveRecord>>)>>();
                */

            // Add SolveRecords to EncodeRecords
            runs.iter().for_each(|(path, run)| {
                let path = path.join("stats/solves");
                fs::read_dir(path).unwrap().for_each(|f| {
                    let (key, solve_records) = serde_json::from_str::<(String, Vec<SolveRecord>)>(
                        &fs::read_to_string(f.unwrap().path()).unwrap(),
                    )
                    .unwrap();
                    let key = get_key(run, &PathBuf::from(&key));
                    // Ignore vacant entries
                    if let Entry::Occupied(entry) = data.entry(key) {
                        let entry = entry.into_mut();
                        if entry.1.is_empty() {
                            entry.1.push(solve_records);
                        } else {
                            entry.1 = vec![solve_records]; // TODO assuming no seeded solver runs
                                                           // assert!(
                                                           //     entry.1.iter().all(|s| s == &solve_records),
                                                           //     "{entry:?} !=\n{solve_records:?}"
                                                           // );
                        }
                    };
                })
            });

            // Assume empty solves are Encoding timeouts
            let data = data
                .into_values()
                .map(|(enc_rec, solves)| {
                    (
                        enc_rec,
                        if solves.is_empty() {
                            vec![vec![SolveRecord {
                                status: Status::Error(EncodeErr::Timeout),
                                ..SolveRecord::default()
                            }]]
                        } else if solves[0]
                            == vec![SolveRecord {
                                status: Status::Error(EncodeErr::Error(String::from(
                                    "Trivial SAT (presumably)",
                                ))),
                                ..SolveRecord::default()
                            }]
                        {
                            vec![vec![SolveRecord {
                                status: Status::Unsat,
                                ..SolveRecord::default()
                            }]]
                        } else {
                            solves
                        },
                    )
                })
                .collect::<Vec<_>>();

            if check {
                check_solve_records(&data);
            }

            // Aggregate SolveRecords into (single) SolveResult
            let data = data
                .into_iter()
                .flat_map(|(enc_rec, solves)| {
                    solves
                        .into_iter()
                        .map(|solve_records| {
                            (
                                enc_rec.clone(),
                                SolveResult::from_solve_records(
                                    &solve_records,
                                    // enc_rec.obj.as_ref().unwrap(),
                                    &Obj::Satisfy,
                                ),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            // Get remaining paths (and instantiate writer)
            let (mut csv, plots, jsons) = {
                let save_to = save_to.unwrap_or_else(|| runs.first().unwrap().0.clone());
                (
                    csv::Writer::from_writer(File::create(save_to.join("res.csv")).unwrap()),
                    save_to.join("plots"),
                    save_to.join("jsons"),
                )
            };

            // Write results to csv file
            for (encode_record, solve_result) in &data {
                #[derive(Serialize)]
                struct CsvRecord {
                    problem: PathBuf,
                    inst_seed: u64,
                    solve_seed: usize,
                    int_encoding: IntEncoding,
                    pb_encoding: PbEncoding,
                    con_encoding: ConEncoding,
                    add_consistency: AddConsistency,
                    cutoff: Option<C>,
                    sort_same_coefficients: usize,
                    system: System,
                    model_config: String,
                    split_eq: bool,
                    propagate: bool,
                    status: Status,
                    enc_time: Option<f32>,
                    first_solve_time: Option<f32>,
                    total_solve_time: Option<f32>,
                    obj: Option<C>,
                    vars: usize,
                    cls: usize,
                    lits: usize,
                    lin_eqs: u32,
                    lin_les: u32,
                    card_eqs: u32,
                    card_les: u32,
                    amo_eqs: u32,
                    amo_les: u32,
                    trivs: u32,
                }

                // TODO
                let inst_seed = 42;
                let StaticsRecord { vars, cls, lits } =
                    encode_record.statics.clone().unwrap_or_default();

                let PbStaticsRecord {
                    lin_eqs,
                    lin_les,
                    card_eqs,
                    card_les,
                    amo_eqs,
                    amo_les,
                    trivs,
                } = encode_record.pb_statics.clone().unwrap_or_default();

                let exp = encode_record.experiment.as_ref().unwrap().clone();
                // TODO denote instance parameters
                csv.serialize(CsvRecord {
                    problem: encode_record.instance.as_ref().unwrap().lp.clone(),
                    inst_seed,
                    solve_seed: 42,
                    int_encoding: exp.int_encoding,
                    pb_encoding: exp.pb_encoding,
                    con_encoding: exp.con_encoding,
                    add_consistency: exp.add_consistency,
                    cutoff: exp.model_config.cutoff,
                    model_config: format!("{:?}", exp.model_config),
                    sort_same_coefficients: exp.sort_same_coefficients,
                    system: exp.system,
                    split_eq: exp.split_eq,
                    propagate: exp.propagate,
                    enc_time: encode_record.time,
                    status: solve_result.status.clone(),
                    first_solve_time: solve_result.first_solve_time,
                    total_solve_time: solve_result.total_solve_time,
                    obj: solve_result.obj,
                    vars,
                    cls,
                    lits,
                    lin_eqs,
                    lin_les,
                    card_eqs,
                    card_les,
                    amo_eqs,
                    amo_les,
                    trivs,
                })
                .unwrap();
            }

            let instance_metrics = data
                .iter()
                .into_group_map_by(|(enc_rec, _)| {
                    enc_rec
                        .instance
                        .as_ref()
                        .unwrap()
                        .lp
                        .clone()
                        .file_name()
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .to_string()
                })
                .into_iter()
                .map(|(instance, all_instance_solve_results)| {
                    (
                        instance,
                        agg(all_instance_solve_results
                            .into_iter()
                            .map(|(_, solve_results)| solve_results)
                            .collect::<Vec<_>>()
                            .as_slice()),
                    )
                })
                .collect::<HashMap<_, _>>();

            // Calculate obj factor
            let data = data
                .into_iter()
                .filter_map(|(encode_record, solve_result)| {
                    let instance = encode_record.instance.as_ref().unwrap();

                    let instance_metrics = &instance_metrics[&instance
                        .lp
                        .file_name()
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .to_string()];

                    // Filter out trivial UNSAT
                    if matches!(instance.problem, Problem::Mbkp { .. })
                        && instance_metrics.3
                        && filter_triv_unsat
                    // && false
                    {
                        return None;
                    }
                    // if matches!(instance.problem, Problem::Mbkp { n_, .. } if n_ != 15) {
                    //     return None;
                    // }
                    // let obj_factor = solve_result.get_obj_factor(
                    //     instance_metrics.2.map(|(min_obj, max_obj)| {
                    //         if encode_record.obj.as_ref().unwrap().is_maximize() {
                    //             max_obj
                    //         } else {
                    //             min_obj
                    //         }
                    //     }),
                    //     PAR,
                    // );
                    let obj_factor = 0.0;
                    Some((encode_record, solve_result, obj_factor))
                })
                .collect::<Vec<_>>();

            let mut tex_rows: HashMap<(&Experiment, &Problem), String> = HashMap::new();

            for (&problem, data) in data
                .iter()
                .into_group_map_by(|(EncodeRecord { instance, .. }, _, _)| {
                    &instance.as_ref().unwrap().problem
                })
                .iter()
                .sorted_by_key(|(problem, _)| **problem)
            {
                // Show summary table
                // let obj = data.first().unwrap().0.obj.as_ref().unwrap();
                let obj = &Obj::Satisfy;

                #[derive(Debug)]
                struct ExperimentMetrics<'a> {
                    statuses: HashMap<&'a Status, usize>,
                    solved: usize,
                    first_solve: f32,
                    total_solve: f32,
                    enc: f32,
                    obj_fac: f32,
                    avg_vars: f32,
                    avg_cls: f32,
                    avg_lits: f32,
                }

                #[derive(Debug, Tabled, Clone)]
                struct SummaryRow {
                    experiment: String,
                    statuses: String,
                    solved: String,
                    first_solve: String,
                    total_solve: String,
                    enc: String,
                    obj_fac: String,
                    avg_vars: String,
                    avg_cls: String,
                    avg_lits: String,
                }

                let experiment_metrics = data
                    .iter()
                    .into_group_map_by(|(EncodeRecord { experiment, .. }, _, _)| {
                        experiment.as_ref().unwrap()
                    })
                    .into_iter()
                    .map(|(experiment, data)| {
                        let inputs = data
                            .iter()
                            .filter_map(
                                |(EncodeRecord { time, statics, .. }, solve_result, obj_factor)| {
                                    if matches!(solve_result.status, Status::Skipped) {
                                        return None;
                                    }

                                    Some((
                                        &solve_result.status,
                                        solve_result.first_solve_time,
                                        solve_result.total_solve_time,
                                        *time,
                                        Some(*obj_factor),
                                        statics.clone().unwrap_or_default(), // TODO
                                    ))
                                },
                            )
                            .collect::<Vec<_>>();

                        let (
                            _,
                            first_solve_times,
                            total_solve_times,
                            enc_times,
                            obj_factors,
                            statics,
                        ): (
                            Vec<_>,
                            Vec<_>,
                            Vec<_>,
                            Vec<_>,
                            Vec<_>,
                            Vec<_>,
                        ) = multiunzip(inputs);

                        let (varss, clss, litss): (Vec<_>, Vec<_>, Vec<_>) = multiunzip(
                            statics
                                .into_iter()
                                .map(|StaticsRecord { vars, cls, lits }| {
                                    (Some(vars as f32), Some(cls as f32), Some(lits as f32))
                                })
                                .collect::<Vec<_>>(),
                        );

                        let statuses = data
                            .iter()
                            .map(|(_, solve_result, _)| &solve_result.status)
                            .counts();

                        fn solved(statuses: &HashMap<&Status, usize>, obj: &Obj<Lit, C>) -> usize {
                            let solved_statuses = if obj.is_satisfy() {
                                vec![Status::Sat, Status::Unsat]
                            } else {
                                vec![Status::Opt]
                            };
                            solved_statuses
                                .iter()
                                .map(|solved_status| statuses.get(&solved_status).unwrap_or(&0))
                                .sum::<usize>()
                        }

                        let solved = solved(&statuses, obj);
                        (
                            experiment,
                            ExperimentMetrics {
                                statuses,
                                solved,
                                first_solve: avg(&first_solve_times, None).unwrap_or(f32::NAN),
                                total_solve: avg(&total_solve_times, None).unwrap_or(f32::NAN),
                                enc: avg(&enc_times, None).unwrap_or(f32::NAN),
                                obj_fac: avg(&obj_factors, None).unwrap_or(f32::NAN),
                                avg_vars: avg(&varss[..], None).unwrap_or(f32::NAN),
                                avg_cls: avg(&clss[..], None).unwrap_or(f32::NAN),
                                avg_lits: avg(&litss[..], None).unwrap_or(f32::NAN),
                            },
                        )
                    })
                    .collect::<HashMap<_, _>>();

                let table = experiment_metrics
                    .iter()
                    .sorted_by(|(_, x), (_, y)| {
                        x.solved
                            .cmp(&y.solved)
                            .reverse()
                            .then(x.total_solve.total_cmp(&y.total_solve))
                    })
                    .map(|(experiment, m)| {
                        let all_statuses = vec![
                            (!obj.is_satisfy()).then_some((Status::Opt, "OPT")),
                            Some((Status::Sat, "SAT")),
                            Some((Status::Unsat, "UNS")),
                            Some((Status::Unknown, "UNK")),
                            Some((Status::Error(EncodeErr::Memory), "MEM")),
                            Some((Status::Error(EncodeErr::Timeout), "ETO")),
                        ]
                        .into_iter()
                        .flatten()
                        .collect::<Vec<_>>();

                        fn display_f32(x: f32) -> String {
                            if x.is_nan() {
                                String::from("T/O")
                            } else {
                                format!("{:.2}", x)
                            }
                        }

                        SummaryRow {
                            statuses: format!(
                                "{} ({})",
                                all_statuses
                                    .iter()
                                    .map(|(status, string)| {
                                        let count = m.statuses.get(status).unwrap_or(&0);
                                        format!("{string}: {count}",)
                                    })
                                    .chain([format!(
                                        "ERR: {}",
                                        m.statuses
                                            .iter()
                                            .filter_map(|(s, count)| matches!(s, Status::Error(_))
                                                .then_some(count))
                                            .sum::<usize>()
                                    )])
                                    .join(", "),
                                m.statuses.values().sum::<usize>()
                            ),
                            experiment: experiment.to_string(),
                            solved: m.solved.to_string(),
                            first_solve: display_f32(m.first_solve),
                            total_solve: display_f32(m.total_solve),
                            enc: display_f32(m.enc),
                            obj_fac: display_f32(m.obj_fac),
                            avg_vars: display_f32(m.avg_vars),
                            avg_cls: display_f32(m.avg_cls),
                            avg_lits: display_f32(m.avg_lits),
                        }
                    })
                    //.sorted_by_key(|row| row.experiment)
                    .collect::<Vec<_>>();
                let mut tabled = Table::new(table.clone());

                if obj.is_satisfy() {
                    tabled.with(Disable::column(ByColumnName::new("first_solve")));
                    tabled.with(Disable::column(ByColumnName::new("obj_fac")));
                }

                println!("== {:?} (T/O = {solver_timeout}) ==", problem);
                println!("{}", tabled);

                let _experiment_status_totals = experiment_metrics
                    .iter()
                    .map(|(e, m)| (e, m.statuses.values().sum::<usize>()))
                    .collect::<HashMap<_, _>>();

                // assert!(
                //     _experiment_status_totals.values().all_equal(),
                //     "{_experiment_status_totals:#?}"
                // );
                if name.contains("pbc") {
                    PBC_PB_ENCS.iter().for_each(|pb_encoding| {
                        let experiment_metrics = experiment_metrics
                            .iter()
                            .filter(|(experiment, _)| {
                                pbc_filter_experiments(experiment, pb_encoding)
                            })
                            .collect::<HashMap<_, _>>();

                        let best = experiment_metrics
                            .iter()
                            .filter(|(exp, _)| *pb_encoding == exp.pb_encoding)
                            .max_by(|(_, x), (_, y)| {
                                x.solved
                                    .cmp(&y.solved)
                                    .then(x.total_solve.total_cmp(&y.total_solve).reverse())
                            })
                            .unwrap()
                            .0;

                        for (
                            experiment,
                            ExperimentMetrics {
                                solved,
                                total_solve,
                                avg_vars,
                                avg_cls,
                                statuses,
                                ..
                            },
                        ) in experiment_metrics.iter().sorted_by_key(|m| m.0)
                        {
                            // let m = experiment_metrics.get(experiment).unwrap();
                            let errs = statuses
                                .iter()
                                .filter_map(|(status, cnt)| {
                                    matches!(status, Status::Error(_)).then_some(cnt)
                                })
                                .sum::<usize>();
                            let (avg_vars, avg_cls) = (
                                avg_vars / (10.0_f32.powi(MAG)),
                                (avg_cls / (10.0_f32.powi(MAG))),
                            );

                            fn display_f32(val: f32, precision: usize) -> String {
                                if val.is_nan() {
                                    String::from("-")
                                } else {
                                    format!("{:.prec$}", val, prec = precision)
                                }
                            }

                            let solved = if solved == &0 {
                                String::from("0")
                            } else {
                                format!("{solved} ({total_solve:.1})").to_string()
                            };

                            let statics = if avg_vars.is_nan() {
                                String::from("-")
                            } else {
                                format!("{}/{}", display_f32(avg_vars, 0), display_f32(avg_cls, 0))
                                    .to_string()
                            };

                            tex_rows.insert(
                                (experiment, problem),
                                if experiment == best {
                                    format!("\\textbf{{{solved}}} & {statics} & {errs}")
                                } else {
                                    format!("{solved} & {statics} & {errs}")
                                },
                            );
                        }
                    });
                }

                // Aggregate the experiments
                let count_max = experiment_metrics
                    .into_values()
                    .map(|m| {
                        m.statuses
                            .into_iter()
                            .filter_map(|(status, count)| {
                                (matches!(status, Status::Opt | Status::Sat | Status::Unsat))
                                    .then_some(count)
                            })
                            .sum::<usize>()
                    })
                    .max()
                    .unwrap_or(0);

                // Aggregate the problems
                let _problem_solve_time_minmax = data
                    .iter()
                    .into_grouping_map_by(|(enc_rec, _, _)| {
                        enc_rec.instance.as_ref().unwrap().problem.clone()
                    })
                    .minmax_by(|_, (_, x, _), (_, y, _)| {
                        x.total_solve_time.partial_cmp(&y.total_solve_time).unwrap()
                    });

                let problem_obj_minmax = data
                    .iter()
                    .into_grouping_map_by(|(enc_rec, _, _)| {
                        enc_rec.instance.as_ref().unwrap().problem.clone()
                    })
                    .minmax_by_key(|_, (_, solve_result, _)| solve_result.obj);

                let _problem_obj_factor_minmax = data
                    .iter()
                    .into_grouping_map_by(|(enc_rec, _, _)| {
                        enc_rec.instance.as_ref().unwrap().problem.clone()
                    })
                    .minmax_by(|_, (_, _, x), (_, _, y)| x.total_cmp(y));

                // .collect::<HashMap<_, _>>();

                // let paths = experiment_metrics.iter().map(|(exp, experiment_metrics)|
                //                                           )

                // return Ok(());

                /*
                            // Write results for each problem and experiment to json files for plotting with mkplot
                            let paths =
                                // data
                                // .iter().cloned()
                            // .into_group_map_by(|(enc_rec,_,_)| (Some(enc_rec.instance.as_ref().unwrap().problem.clone()), enc_rec.experiment.as_ref().unwrap().clone()))
                            // .iter()
                            // .chain(
                                // g.iter()
                                // // experiment_metrics.iter().map(|(exp, exp_m)| s)
                            // )

                                g.iter()
                            .filter_map(|(json, (ys, prog_alias, program, linestyle))| {
                                // let experiment_name = format!("{}", experiment);

                                // let linestyle = match experiment {
                                //     Experiment { con_encoding: ConEncoding::Ignore, propagate: false, add_consistency: AddConsistency::Skip, system: System::Pbc, ..} => 0,
                                //     Experiment { con_encoding: ConEncoding::Include, split_eq: true, propagate: false, add_consistency: AddConsistency::Skip, system: System::Pbc, ..} => 1,
                                //     Experiment { con_encoding: ConEncoding::Include, split_eq: false, propagate: false, add_consistency: AddConsistency::Skip, system : System::Pbc, ..} => 2,
                                //     Experiment { con_encoding: ConEncoding::Include, split_eq: false, propagate: true, add_consistency: AddConsistency::Skip, system: System::Pbc, ..} => 3,
                                //     Experiment { con_encoding: ConEncoding::Include, add_consistency: AddConsistency::Aux, system: System::Pbc, ..} => 4,
                                //     Experiment { system: System::SavileRow, ..} => 5,
                                //     Experiment { system: System::PbLib, ..} => 6,
                                //     _ => { println!("WARNING: No linestyle set for {experiment:?}"); 6} ,
                                // };


                                // Plot scatter plots
                                if scatter {
                                    todo!("scatter not supported at the moment; fix result filtering + save jsons separately");
                                }

                //                 let stats = solves
                //                     .iter()
                //                     .filter(|(_, solve_result, _)| {
                //                         matches!(
                //                             solve_result.status,
                //                             Status::Sat | Status::Opt | Status::Unsat
                //                         )
                //                     })
                //                     .flat_map(|(EncodeRecord { instance, statics, .. }, solve_result, obj_factor)| {
                //                         let statics = statics.clone().unwrap_or_default();
                //                         let instance = instance.as_ref().unwrap();
                //                         assert!(!matches!(solve_result.status, Status::Error(_)));

                //                         let (status, first_solve_time, total_solve_time)  = if scatter  {
                //                             (solve_result.status != Status::Unknown, solve_result.first_solve_time.unwrap_or(solver_timeout), solve_result.total_solve_time.unwrap_or(solver_timeout))
                //                         } else if solve_result.status == Status::Unknown {
                //                                 return None;
                //                             } else {
                //                                 (true, solve_result.first_solve_time.unwrap(), solve_result.total_solve_time.unwrap())
                //                         };

                //                         Some((
                //                             format!("{}", instance.i),
                //                             json!({
                //                                 "status": status,
                //                                 "first_solve_time": first_solve_time,
                //                                 "total_solve_time": total_solve_time,
                //                                 "cost": solve_result.obj,
                //                                 "obj_factor": obj_factor,
                //                                 "vars": statics.vars,
                //                                 "cls": statics.cls,
                //                                 "lits": statics.lits,
                //                                 "solve_status": solve_result.status,
                //                             }),
                //                         ))
                //                     })
                //                     .collect::<HashMap<_, _>>();

                                // if stats.is_empty() {
                                //     return None;
                                // }

                                let path = jsons.join(json);

                                to_writer_pretty(BufWriter::new(File::create(&path).unwrap()), &json!({
                                    "preamble": {
                                    "benchmark": String::from("pbp"),
                                    "program": program,
                                    // "prog_alias": to_alias(experiment, problem.as_ref()),
                                    "prog_alias": prog_alias,
                                    "linestyle": linestyle
                                    },
                                    "stats": {}}
                                ))

                                    .unwrap();
                                // Some((experiment.clone(), path))
                                path
                            })
                            .collect::<HashMap<_, _>>();

                            for (_, pb_enc) in [PbEncoding::Gt].into_iter().enumerate() {
                                /*
                                let vbs = vbs
                                    .then(|| {
                                        vec![
                                            get_vb(
                                                &experiment_metrics,
                                                &paths,
                                                HashSet::from([System::SavileRow, System::SavileRowBasic]),
                                            ),
                                            get_vb(&experiment_metrics, &paths, HashSet::from([System::PbLib])),
                                        ]
                                        .into_iter()
                                        .flatten()
                                        .collect::<Vec<_>>()
                                    })
                                    .unwrap_or_default();
                                    */
                                // let vbs = None;

                                let paths = paths
                                    .clone()
                                    .into_iter()
                                    //.filter(|(exp, _)| {
                                    //    exp.pb_encoding == pb_enc
                                    //    // && exp.system == System::Pbc
                                    //    //matches!(
                                    //    //    exp,
                                    //    //    Experiment {
                                    //    //        pb_encoding: pb_enc,
                                    //    //        system: System::Pbc,
                                    //    //        ..
                                    //    //    }
                                    //    //)
                                    //})
                                    // .filter(|(exp, _)| {
                                    //     matches!(
                                    //         exp,
                                    //         Experiment {
                                    //             // show PbLib (only ord
                                    //             system: System::PbLib,
                                    //             int_encoding: IntEncoding::Ord,
                                    //             ..
                                    //         } | Experiment {
                                    //             //show SR
                                    //             system: System::SavileRow | System::SavileRowBasic,
                                    //             ..
                                    //         } | Experiment {
                                    //             // show basic
                                    //             con_encoding: ConEncoding::Ignore,
                                    //             split_eq: true,
                                    //             propagate: false,
                                    //             ..
                                    //         } | Experiment {
                                    //             // show int
                                    //             con_encoding: ConEncoding::Include,
                                    //             split_eq: true,
                                    //             propagate: false,
                                    //             ..
                                    //         } | Experiment {
                                    //             // show eqs
                                    //             con_encoding: ConEncoding::Include,
                                    //             split_eq: false,
                                    //             propagate: false,
                                    //             ..
                                    //         } | Experiment {
                                    //             // show all
                                    //             con_encoding: ConEncoding::Include,
                                    //             split_eq: false,
                                    //             propagate: true,
                                    //             ..
                                    //         }
                                    //     )
                                    // })
                                    // .filter(|(exp, _)| {
                                    //     !matches!(
                                    //         exp,
                                    //         Experiment {
                                    //             pb_encoding: PbEncoding::Bdd,
                                    //             propagate: true,
                                    //             ..
                                    //         }
                                    //     )
                                    // })
                                    // .chain(vbs)
                                    .collect::<HashMap<_, _>>();

                                let x_min_max = (0.0, count_max as f32);

                                let problem_name = problem.to_string().replace('/', "_");
                                let (name, key, y_min_max) = if matches!(obj, Obj::Satisfy) {
                                    (
                                        Some(format!("cactus_sat_{}_{:?}", problem_name, pb_enc)),
                                        "first_solve_time",
                                        (0.1, solver_timeout),
                                    )
                                } else {
                                    (
                                        Some(format!("cactus_obj_{}_{:?}", problem_name, pb_enc)),
                                        "obj_factor",
                                        match problem_obj_minmax[problem] {
                                            MinMaxResult::NoElements => panic!(),
                                            MinMaxResult::OneElement(_) => panic!(),
                                            MinMaxResult::MinMax((_, _, min), (_, _, max)) => (*min, *max),
                                        },
                                    )
                                };

                                if !paths.is_empty() {
                                    plot_cactus(
                                        paths.values().cloned().collect(),
                                        PlotType::Cactus,
                                        name,
                                        solver_timeout,
                                        x_min_max,
                                        y_min_max,
                                        key,
                                        y_log,
                                        plots.clone(),
                                        &fmt,
                                        //i + 1,
                                        0,
                                    );

                                    if scatter {
                                        for ((exp_a, path_a), (exp_b, path_b)) in paths.iter().tuple_combinations()
                                        {
                                            //let ((exp_a, path_a), (exp_b, path_b)) = if exp_a > exp_b {
                                            //    ((exp_b, path_b), (exp_a, path_a))
                                            //} else {
                                            //    ((exp_a, path_a), (exp_b, path_b))
                                            //};

                                            let name = Some(format!(
                                                "scatter_sat_{}_{}",
                                                path_a.file_name().unwrap().to_str().unwrap(),
                                                path_b.file_name().unwrap().to_str().unwrap()
                                            ));
                                            plot_cactus(
                                                vec![path_a.to_path_buf(), path_b.to_path_buf()],
                                                PlotType::Scatter(exp_a.clone(), exp_b.clone()),
                                                name,
                                                solver_timeout,
                                                y_min_max,
                                                y_min_max,
                                               key,
                                                y_log,
                                                plots.clone(),
                                                &fmt,
                                                0,
                                            );
                                        }
                                    }
                                }
                            }

                            */
            }

            if plot {
                name.contains("scm")
                    .then(|| {
                        let (xys_solve, xys_vars, xys_cls, xys_lits): (
                            Vec<_>,
                            Vec<_>,
                            Vec<_>,
                            Vec<_>,
                        ) = data
                            .iter()
                            .cloned()
                            .into_group_map_by(|(enc_rec, _, _)| {
                                enc_rec.experiment.as_ref().unwrap().clone()
                                // Some(enc_rec.instance.as_ref().unwrap().problem.clone()),
                                // if let Instance {
                                //     problem: Problem::Mbkp { bound, .. },
                                //     ..
                                // } = enc_rec.instance.unwrap()
                                // {
                                //     bound
                                // } else {
                                //     panic!()
                                // },
                            })
                            .into_iter()
                            .map(|(experiment, res)| {
                                // let (xy_solve, xy_vars, xy_cls, xy_lits): (Vec<_>, Vec<_>, Vec<_>, Vec<_>) = res
                                let res = res
                                    .iter()
                                    .into_group_map_by(|(enc_rec, solves, _)| {
                                        enc_rec.instance.as_ref().unwrap().problem.mbkp_bit_width()
                                    })
                                    .into_iter()
                                    .sorted_by_key(|(bound, _)| *bound)
                                    .collect_vec();

                                let xy_solve = res
                                    .iter()
                                    .map(|(x, ys)| {
                                        let ys_solve_times = ys
                                            .iter()
                                            .map(|(_, solve, _)| solve.first_solve_time)
                                            .collect::<Vec<_>>();
                                        (
                                            format!("{}", x),
                                            if ys_solve_times.iter().any(|y| y.is_some()) {
                                                // TODO change avg to return Option if all is None
                                                avg(&ys_solve_times, Some(solver_timeout * PAR))
                                            } else {
                                                None
                                            },
                                        )
                                    })
                                    .collect();

                                let (xy_vars, xy_cls, xy_lits): (Vec<_>, Vec<_>, Vec<_>) = res
                                    .iter()
                                    .map(|(x, ys)| {
                                        let static_avg =
                                            |statics: &[Option<f32>]| avg(&statics, None);
                                        let (ys_vars, ys_cls, ys_lits): (Vec<_>, Vec<_>, Vec<_>) =
                                            ys.iter()
                                                .map(|(enc, _, _)| {
                                                    enc.statics
                                                        .as_ref()
                                                        .map(|s| {
                                                            (
                                                                Some(s.vars as f32),
                                                                Some(s.cls as f32),
                                                                Some(s.lits as f32),
                                                            )
                                                        })
                                                        .unwrap_or((None, None, None))
                                                    // enc.statics.as_ref().map(|s| s.variables as f32)
                                                })
                                                .multiunzip();
                                        let (y_vars, y_cls, y_lits) = (
                                            static_avg(&ys_vars),
                                            static_avg(&ys_cls),
                                            static_avg(&ys_lits),
                                        );
                                        (
                                            (format!("{}", x), y_vars),
                                            (format!("{}", x), y_cls),
                                            (format!("{}", x), y_lits),
                                        )
                                    })
                                    .multiunzip();

                                let skip_min_max = experiment.model_config.scm == Scm::Dnf;
                                (
                                    MkplotConfig::scm(
                                        &experiment,
                                        xy_solve,
                                        PathBuf::from(format!("{}-solve.json", experiment)),
                                        false,
                                    ),
                                    MkplotConfig::scm(
                                        &experiment,
                                        xy_vars,
                                        PathBuf::from(format!("{}-vars.json", experiment)),
                                        skip_min_max,
                                    ),
                                    MkplotConfig::scm(
                                        &experiment,
                                        xy_cls,
                                        PathBuf::from(format!("{}-cls.json", experiment)),
                                        skip_min_max,
                                    ),
                                    MkplotConfig::scm(
                                        &experiment,
                                        xy_lits,
                                        PathBuf::from(format!("{}-lits.json", experiment)),
                                        skip_min_max,
                                    ),
                                )
                            })
                            .multiunzip();
                        let x_label = String::from("Bit width [\\#bits]");
                        let static_title = String::from("MBKP (static)");
                        let loc = String::from("lower right");

                        [
                            Mkplot {
                                title: String::from("MBKP"),
                                plot_type: PlotType::Instance,
                                x_label: x_label.clone(),
                                y_label: String::from("Solve time [s] (PAR2)"),
                                save_to: String::from("mbkp-solve"),
                                xys: xys_solve,
                                log: false,
                                loc: loc.clone(),
                            },
                            Mkplot {
                                title: static_title.clone(),
                                plot_type: PlotType::Instance,
                                x_label: x_label.clone(),
                                y_label: String::from("Variables"),
                                save_to: String::from("mbkp-variables"),
                                xys: xys_vars,
                                log: true,
                                loc: loc.clone(),
                            },
                            Mkplot {
                                title: static_title.clone(),
                                plot_type: PlotType::Instance,
                                x_label: x_label.clone(),
                                y_label: String::from("Clauses"),
                                save_to: String::from("mbkp-clauses"),
                                xys: xys_cls,
                                log: true,
                                loc: loc.clone(),
                            },
                            Mkplot {
                                title: static_title,
                                plot_type: PlotType::Instance,
                                x_label,
                                y_label: String::from("Literals"),
                                save_to: String::from("mbkp-literals"),
                                xys: xys_lits,
                                log: true,
                                loc: loc.clone(),
                            },
                        ]
                    })
                    .into_iter()
                    .flatten()
                    .chain(
                        (name.contains("pbc"))
                            .then(|| {
                                // PBC plots
                                data.iter()
                                    .cloned()
                                    .into_group_map_by(|(enc_rec, _, _)| {
                                        enc_rec.instance.as_ref().unwrap().problem.clone()
                                    })
                                    .into_iter()
                                    .sorted_by_key(|(problem, _)| problem.clone())
                                    .enumerate()
                                    .flat_map(|(i, (problem, res))| {
                                        PBC_PB_ENCS
                                            .iter()
                                            .map(|pb_encoding| {
                                                Mkplot {
                                                    log: false,
                                                    loc: String::from("upper left"),
                                                    title: format!("{problem}_{pb_encoding:?}")
                                                        .to_string(),
                                                    plot_type: PlotType::Cactus,
                                                    x_label: String::from("Solved [\\#instances]"),
                                                    y_label: String::from("Solve time [s]"),
                                                    save_to: format!(
                                                        "{}_{}_{:?}",
                                                        match problem {
                                                            Problem::Mbkp { .. } => "mbkp",
                                                            Problem::RandEqs { .. } => "mbssp",
                                                            _ => todo!(),
                                                        },
                                                        i + 1,
                                                        pb_encoding
                                                    )
                                                    .to_string(),
                                                    // save_to: format!("{problem}_{pb_encoding:?}")
                                                    //     .to_string(),
                                                    xys: res
                                                        .iter()
                                                        .filter(|(enc, _, _)| {
                                                            pbc_filter_experiments(
                                                                enc.experiment.as_ref().unwrap(),
                                                                pb_encoding,
                                                            )
                                                        })
                                                        // split up per experiment
                                                        .into_group_map_by(|(enc_rec, _, _)| {
                                                            enc_rec
                                                                .experiment
                                                                .as_ref()
                                                                .unwrap()
                                                                .clone()
                                                        })
                                                        .into_iter()
                                                        .map(|(experiment, res)| {
                                                            let (prog_alias, linestyle) = to_alias(
                                                                &experiment,
                                                                Some(&problem),
                                                            );
                                                            MkplotConfig {
                                                                prog_alias,
                                                                program: format!("{}", experiment),
                                                                linestyle,
                                                                xy: res
                                                                    .into_iter()
                                                                    .map(|(enc_rec, solve, _)| {
                                                                        (
                                                                            format!(
                                                                                "{}",
                                                                                enc_rec
                                                                                    .instance
                                                                                    .as_ref()
                                                                                    .unwrap()
                                                                                    .i
                                                                            ),
                                                                            solve.first_solve_time,
                                                                        )
                                                                    })
                                                                    .collect(),
                                                                path: PathBuf::from(format!(
                                                                    "{}-{}-solve.json",
                                                                    problem, experiment
                                                                )),
                                                                skip_min_max: false,
                                                            }
                                                        })
                                                        .collect(),
                                                }
                                            })
                                            .collect_vec()
                                    })
                            })
                            .into_iter()
                            .flatten(),
                    )
                    .for_each(|mkplot| {
                        mkplot.plot(&jsons, &plots, &fmt);
                    });
            }

            if TEX && name.contains("pbc") {
                let (mbssp, mbkp): (Vec<_>, Vec<_>) = data
                    .iter()
                    .map(|(e, _, _)| e.instance.as_ref().unwrap().problem.clone())
                    .unique()
                    .partition(|problem| matches!(problem, Problem::RandEqs { .. }));

                for instance_sets in [mbssp, mbkp]
                    .into_iter()
                    .filter(|instance_set| !instance_set.is_empty())
                {
                    let instance_sets = instance_sets.into_iter().sorted().collect_vec();
                    let problem = instance_sets.first().unwrap();
                    let problem_lbl = match problem {
                        Problem::Soh { .. } => String::from("soh"),
                        Problem::Mbkp { .. } => String::from("mbkp"),
                        Problem::RandEqs { .. } => String::from("mbssp"),
                        _ => todo!(),
                    };

                    // let out = format!("./tex/figures/plots/{problem_lbl}.tex");
                    let out = format!("./tex/pbc/res/{problem_lbl}.tex");
                    //let header = &["solved (time)", "vars/cls ($10^3$)", "err"];
                    // let header = &["solved", "size", "err"];
                    let problems = 3;
                    let header_names = &["solved", "size", "err"];
                    let cols = 1 + header_names.len() * problems;

                    let alignment = "l"; // c/r/l..
                    let cs = (0..cols).map(|_| alignment).join("|");
                    let header = header_names.join(" & ");
                    let mut tex = String::new();
                    use std::fmt::Write;
                    writeln!(tex, "\\begin{{tabular}}{{ |{cs}| }}").unwrap();
                    //writeln!(tex, "\\hline").unwrap();
                    //writeln!(tex, "{header}\\\\").unwrap();
                    //writeln!(tex, "\\hline").unwrap();
                    writeln!(tex, "\\cline{{2-{cols}}}").unwrap();

                    //write!(tex, "experiment").unwrap();

                    writeln!(tex, "\\multicolumn{{1}}{{c|}}{{}}",).unwrap();

                    for problem in &instance_sets {
                        write!(
                            tex,
                            " & \\multicolumn{{{}}}{{c|}}{{{}}}",
                            header_names.len(),
                            problem.to_problem_label()
                        )
                        .unwrap();
                    }
                    writeln!(tex, "\\\\").unwrap();
                    writeln!(tex, "\\cline{{2-{cols}}}").unwrap();

                    writeln!(tex, "\\multicolumn{{1}}{{c|}}{{}}").unwrap();
                    for _ in &instance_sets {
                        write!(tex, " & {header}").unwrap();
                    }

                    writeln!(tex, "\\\\").unwrap();
                    writeln!(tex, "\\hline").unwrap();

                    let pbc_experiments = tex_rows
                        .keys()
                        .unique_by(|(e, _)| e)
                        // .filter(|e| {
                        //     !matches!(
                        //         e,
                        //         Experiment {
                        //             pb_encoding: PbEncoding::Bdd,
                        //             propagate: true,
                        //             add_consistency: AddConsistency::Skip,
                        //             system: System::Pbc,
                        //             model_config: ModelConfig { cutoff: None, .. },
                        //             ..
                        //         }
                        //     )
                        // })
                        .map(|(e, p)| (e, p, to_alias(e, Some(p))))
                        .sorted_by_key(|(e, _, alias)| (&e.pb_encoding, alias.1)) // sort by linestyle
                        .collect::<Vec<_>>();

                    for ((experiment, _, (alias, _)), (next_experiment, _, _)) in pbc_experiments
                        .iter()
                        .chain(pbc_experiments.last())
                        .tuple_windows()
                    {
                        write!(tex, "{alias} & ").unwrap();
                        let row = instance_sets
                            .iter()
                            .map(|problem| tex_rows.get(&(*experiment, problem)).unwrap())
                            .join(" & ");
                        write!(tex, "{row}").unwrap();
                        writeln!(tex, "\\\\").unwrap();

                        if experiment.pb_encoding != next_experiment.pb_encoding
                            || next_experiment.system == System::Scop
                        {
                            writeln!(tex, "\\hline").unwrap();
                        }
                    }

                    writeln!(tex, "\\hline").unwrap();

                    writeln!(tex, "\\end{{tabular}}").unwrap();

                    fs::write(out, tex).unwrap();
                }
            }
            Ok(())
        } else {
            unreachable!()
        }
    } else {
        unreachable!()
    }
}

type ExperimentMetric = (HashMap<Status, usize>, f32, f32, f32, f32, f32, f32);

fn get_vb(
    experiment_metrics: &HashMap<&&Experiment, ExperimentMetric>,
    paths: &HashMap<Experiment, PathBuf>,
    systems: HashSet<System>,
) -> Option<(Experiment, PathBuf)> {
    experiment_metrics
        .iter()
        .filter(|(exp, _)| systems.contains(&exp.system))
        .filter(|(_, x)| !x.1.is_nan())
        .min_by(|(_, a), (_, b)| a.1.partial_cmp(&b.1).unwrap())
        .map(|(&&exp, _)| (exp.clone(), paths[exp].clone()))
}

pub enum PlotType {
    Cactus,
    Instance,
    Scatter(Experiment, Experiment),
}

impl Mkplot {
    pub fn plot(&self, jsons: &PathBuf, plots: &PathBuf, fmt: &str) {
        let save_to = format!("{}/{}.{}", plots.display(), &self.save_to, fmt);

        let (paths, xys): (Vec<_>, Vec<_>) = self
            .xys
            .iter()
            .map(|mkplot_config| {
                let path = jsons.join(&mkplot_config.path);
                let stats = mkplot_config
                    .xy
                    .iter()
                    .cloned()
                    .flat_map(|(x, y)| y.map(|y| (x, json!({ "y": y, "status": true}))))
                    // .map(|(x, y)| {
                    //     let status = y.is_some();
                    //     (x, json!({ "y": y.unwrap_or(0), "status": status}))
                    // })
                    // .collect::<Vec<_>>();
                    .collect::<HashMap<_, _>>();
                to_writer_pretty(
                    BufWriter::new(File::create(&path).unwrap()),
                    &json!({
                        "preamble": {
                        "benchmark": String::from("pbp"),
                        "program": mkplot_config.program,
                        // "prog_alias": to_alias(experiment, problem.as_ref()),
                        "prog_alias": mkplot_config.prog_alias,
                        "linestyle": mkplot_config.linestyle
                        },
                        "stats": stats,
                    }),
                )
                .unwrap();

                (path, &mkplot_config.xy)
            })
            .unzip();

        let x_min_max = Some((0.0, xys.iter().map(|xy| xy.len()).max().unwrap() as f32));
        let y_min_max = self
            .xys
            .iter()
            .filter(|conf| !conf.skip_min_max)
            .flat_map(|conf| conf.xy.iter().flat_map(|(_, y)| y))
            .filter(|y| !y.is_nan())
            .copied()
            .minmax()
            .into_option();

        const MARGIN: f32 = 0.1;
        const MIN: f32 = 1.0;

        let process_min_max = |(min, max)| {
            let max = if max - min < MIN { min + MIN } else { max };
            (
                format!("{}", min * (1.0 - MARGIN)),
                format!("{}", max * (1.0 + MARGIN)),
            )
        };

        let x_min_max = x_min_max.map(process_min_max);
        let y_min_max = y_min_max.map(process_min_max);

        let (x_label, y_label) = (
            format!("--xlabel \"{}\"", self.x_label),
            format!("--ylabel \"{}\"", self.y_label),
        );
        let loc = format!("\"{}\"", self.loc);
        let mkplot_cactus = [
            MKPLOT,
            "-l",
            "-p",
            match self.plot_type {
                PlotType::Cactus => "cactus",
                PlotType::Instance => "instance",
                PlotType::Scatter(_, _) => "scatter",
            },
            "--shape",
            "squared",
            "--legend prog_alias",
            // if i == 0 || i == 3 {
            //     "--legend prog_alias"
            // } else {
            //     ""
            // },
            "--lloc",
            &loc,
            // if i == 0 || i == 3 {
            //     "\"upper left\""
            // } else {
            //     "off"
            // },
            // "-t",
            // &timeout,
            &x_label,
            &y_label,
            if self.log { "--ylog" } else { "" },
            "-b",
            &fmt,
            "-k",
            "\"y\"",
            "--by-name",
            "--save-to",
            &save_to,
        ]
        .into_iter()
        .map(|s| s.to_string())
        .chain(
            x_min_max
                .map(|(min, max)| vec![String::from("--xmin"), min, String::from("--xmax"), max])
                .unwrap_or_default(),
        )
        .chain(
            y_min_max
                .map(|(min, max)| vec![String::from("--ymin"), min, String::from("--ymax"), max])
                .unwrap_or_default(),
        )
        .chain(
            paths
                .iter()
                .map(|string| string.to_str().unwrap().to_string()),
        )
        .filter(|arg| !arg.is_empty())
        .collect::<Vec<_>>();

        let mkplot_cactus = &mkplot_cactus.join(" ");
        let args = [mkplot_cactus];

        let output = Command::new(PYTHON).args(args).output().unwrap();
        const OUTPUT_MKPLOT: bool = true;
        if !output.status.success() || OUTPUT_MKPLOT {
            let out = String::from_utf8(output.stdout).unwrap();
            let err = String::from_utf8(output.stderr).unwrap();
            println!("{}\n{}\n{}\n", args.join(" "), out, err);
        }
    }
}

fn check_solve_record(
    model: &Model<Lit, C>,
    solve: &SolveRecord,
    instance: &Instance,
) -> Result<(), CheckError<Lit>> {
    match &solve.status {
        Status::Unsat if matches!(instance.problem, Problem::RandEqs { .. }) => Err(
            CheckError::Fail(format!("Unsat on {instance:?} which is known to be SAT")),
        ),
        Status::Unknown | Status::Unsat | Status::Error(_) | Status::Skipped => Ok(()),
        Status::Sat | Status::Opt => solve
            .assignment
            .as_ref()
            .map(|assignment| {
                model.check_assignment(&Assignment(
                    assignment.iter().map(|(k, v)| (IntVarId(*k), *v)).collect(),
                ))
            })
            .unwrap_or(Ok(())),
        Status::Encoded => unreachable!(),
    }
}

fn get_best_cost(solve_records: &[SolveRecord], is_bkp: bool) -> Option<C> {
    if is_bkp {
        solve_records.iter().flat_map(|s| s.cost).max()
    } else {
        solve_records.iter().flat_map(|s| s.cost).min()
    }
}

fn get_final_status(solve_records: &[SolveRecord]) -> Status {
    match &solve_records
        .iter()
        .map(|r| r.status.clone())
        .collect::<Vec<_>>()[..]
    {
        [] => Status::Encoded,
        [status] => status.clone(),
        xs => {
            let last = &xs[xs.len() - 1];
            if matches!(last, Status::Opt | Status::Unknown) {
                xs[xs.len() - 2].clone()
            } else {
                last.clone()
            }
        }
    }
}

#[derive(Debug, Clone, Serialize, Default)]
struct SolveResult {
    status: Status,
    first_solve_time: Option<f32>,
    total_solve_time: Option<f32>,
    obj: Option<C>,
    //method: Obj,
}

impl SolveResult {
    pub fn from_solve_records(solve_records: &[SolveRecord], obj: &Obj<Lit, C>) -> Self {
        let solve_times = solve_records
            .iter()
            .filter_map(|s| match &s.status {
                Status::Opt | Status::Sat | Status::Unsat => Some(s.time),
                Status::Unknown | Status::Skipped | Status::Error(_) => None,
                unexpected => panic!("Unexpected status {unexpected:?}"),
            })
            .collect::<Vec<_>>();

        Self {
            status: get_final_status(solve_records),
            first_solve_time: solve_times.first().copied(),
            total_solve_time: (!solve_times.is_empty()).then(|| solve_times.iter().sum()),
            obj: get_best_cost(solve_records, obj.is_maximize()),
        }
    }
    pub fn get_obj_factor(&self, best: Option<C>, par: f32) -> f32 {
        if let Some(best) = best {
            self.obj
                .map(|obj| (obj as f32) / (best as f32))
                .unwrap_or(par)
        } else {
            par
        }
    }
}

fn check_solve_records(data: &[(EncodeRecord, Vec<Vec<SolveRecord>>)]) {
    let ilps: HashMap<PathBuf, Model<Lit, C>> = data
        .iter()
        .map(|(encode_record, _)| {
            let lp = encode_record.instance.as_ref().unwrap().lp.clone();
            (lp.clone(), Model::from_file(lp).unwrap())
        })
        .collect();

    // if !instance_aggs
    //     .values()
    //     .tuple_windows()
    //     .all(|(a, b)| a == b)
    // {
    //     println!(
    //         "Experiment counts were not all-equal: {:#?}",
    //         instance_aggs
    //     );
    // }

    data.iter()
        .filter(|(encode_record, _)| {
            encode_record.experiment.as_ref().unwrap().system != System::Scop
        })
        .flat_map(|(encode_record, solves)| {
            solves
                .iter()
                .map(|solves| {
                    (
                        //encode_record.instance.unwrap().lp.clone(),
                        encode_record.instance.as_ref().unwrap(),
                        (encode_record.clone().experiment.unwrap(), solves),
                    )
                })
                .collect::<Vec<_>>()
        })
        .into_group_map()
        .into_iter()
        .flat_map(|(instance, exp_solves)| {
            //println!("Checking {instance:?}");

            let ilp = &ilps[&instance.lp];

            exp_solves
                .clone()
                .into_iter()
                .map(|(exp, solves)| {
                    solves.iter().try_for_each(|solve| {
                        check_solve_record(ilp, solve, instance).map_err(|err| match err {
                            CheckError::Fail(s) => (
                                exp.clone(),
                                CheckError::Fail(
                                    format!("{s}\n{:?}\n{}", exp, instance.lp.display())
                                        .to_string(),
                                ),
                            ),
                            _ => (exp.clone(), err),
                        })
                    })
                })
                .chain([{
                    let instance_solve_records = exp_solves.clone();
                    if instance_solve_records.is_empty() {
                        return vec![Ok(())];
                    }
                    let instance_statuses = instance_solve_records
                        .iter()
                        .map(|(_, solve_records)| get_final_status(solve_records))
                        .filter(|status| !matches!(status, Status::Error(_)))
                        .collect::<Vec<_>>();

                    (!((instance_statuses.contains(&Status::Sat)
                        || instance_statuses.contains(&Status::Opt))
                        && instance_statuses.contains(&Status::Unsat)))
                    .then_some(())
                    .ok_or_else(|| {
                        (
                            exp_solves.first().unwrap().0.clone(),
                            CheckError::Fail(format!("ContradictionError: {:?}\n", instance)),
                        )
                    })
                }])
                .collect::<Vec<_>>()
        })
        .for_each(|res| {
            if let Err((exp, err)) = res {
                println!("{exp:?}: {}", err);
            }
        });
}

fn agg_t<T: PartialOrd + Copy + std::fmt::Debug>(xs: &[T]) -> Option<(T, T)> {
    (!xs.is_empty()).then(|| {
        (
            *xs.iter().min_by(|a, b| a.partial_cmp(b).unwrap()).unwrap(),
            *xs.iter().max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap(),
        )
    })
}

/// Averaging (None's incur penalty)
pub fn avg<T: std::iter::Sum + Copy + Into<f32>>(
    xs: &[Option<T>],
    penalty: Option<T>,
) -> Option<f32> {
    if xs.is_empty() {
        return penalty.map(|p| p.into());
    }
    let xs = xs
        .iter()
        .flat_map(|x| {
            if let Some(penalty) = penalty {
                Some(x.unwrap_or(penalty))
            } else {
                *x
            }
        })
        .collect::<Vec<_>>();
    let n = xs.len() as f32;
    Some(xs.into_iter().clone().sum::<T>().into() / n)
}

fn agg(
    solve_results: &[&SolveResult],
) -> (
    HashMap<Status, usize>,
    Option<(f32, f32)>,
    Option<(C, C)>,
    bool,
) {
    let statuses = solve_results
        .iter()
        .map(|r| (r.status.clone(), 1))
        .into_group_map()
        .into_iter()
        .map(|(status, counts)| (status, counts.len()))
        .collect::<HashMap<_, _>>();
    let times = solve_results
        .iter()
        .flat_map(|r| r.total_solve_time)
        .collect::<Vec<_>>();
    let time_min_max = agg_t(&times);
    let costs = solve_results.iter().flat_map(|r| r.obj).collect::<Vec<_>>();
    let obj_min_max = agg_t(&costs);

    let triv_unsat = solve_results
        .iter()
        .any(|&solve| solve.status == Status::Unsat && solve.first_solve_time.unwrap() == 0.0);

    (statuses, time_min_max, obj_min_max, triv_unsat)
}

const SHOW_EXTS: bool = false;
fn to_alias(experiment: &Experiment, problem: Option<&Problem>) -> (String, usize) {
    let is_mbkp = matches!(problem.unwrap(), Problem::Mbkp { .. });
    let pb_encoding_lbl = format!("{:?}", experiment.pb_encoding).to_uppercase();
    let (lbl, linestyle) = match experiment {
            Experiment {
                system: System::SavileRow,
                pb_encoding,
                ..
            } => (format!("{pb_encoding_lbl} (SavileRow)"), if pb_encoding == &PbEncoding::Gmto { 7} else {6}),
            Experiment {
                system: System::Scop,
                ..
            } => (String::from("Fun-sCOP"), 8),
            Experiment {
                system: System::PbLib,
                ..
            } => (String::from("PBLib"), 9),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                model_config: ModelConfig {cutoff: Some(_), ..},
                ..
            //} => 3,
            } => (format!("{pb_encoding_lbl} (\\texttt{{binary}})"), 5),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                add_consistency: AddConsistency::Aux,
                model_config: ModelConfig {cutoff: None, ..},
                ..
            } => (format!("{pb_encoding_lbl} + \\ldots + \\texttt{{cons}}"), 4),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                propagate: true,
                add_consistency: AddConsistency::Skip,
                model_config: ModelConfig {cutoff: None, ..},
                ..
            //} => 3,
            } if !is_mbkp =>  (format!("{pb_encoding_lbl} + \\ldots + \\texttt{{prop}}"), 3),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                model_config: ModelConfig {cutoff: None, ..},
                ..
            //} if !is_mbkp => 2,
            } if !is_mbkp => (format!("{pb_encoding_lbl} + \\ldots + \\texttt{{eqs}}"), 2),
            Experiment {
                con_encoding: ConEncoding::Include,
                ..
            //} => 1,
            } => (format!("{pb_encoding_lbl} + \\ldots + \\texttt{{int}}"), 1),
            Experiment {
                con_encoding: ConEncoding::Ignore,
                ..
            // } => 0,
            } => (pb_encoding_lbl, 0)
        };

    if SHOW_EXTS {
        let lbl = format!(
            "{}{}{}{}{}{}{} ({})",
            format!("{:?}", experiment.pb_encoding).to_uppercase(),
            if experiment.con_encoding == ConEncoding::Include {
                " + \\texttt{{int}}"
            } else {
                " "
            },
            if !experiment.split_eq
                && !is_mbkp
                && !(matches!(
                    experiment.system,
                    System::SavileRow | System::SavileRowBasic
                ))
            {
                " + \\texttt{{eqs}}"
            } else {
                " "
            },
            if experiment.propagate && !is_mbkp {
                " + \\texttt{{prop}}"
            } else {
                " "
            },
            if experiment.model_config.cutoff.is_some() {
                " + \\texttt{{bin}}"
            } else {
                " "
            },
            if experiment.add_consistency == AddConsistency::Aux {
                " + \\texttt{{cons}}"
            } else {
                " "
            },
            if experiment.system == System::SavileRow {
                format!(" (SR \\texttt{{{:?}}})", experiment.int_encoding)
            } else if experiment.system == System::SavileRowBasic {
                String::from(" (SavileRowBasic)")
            } else if experiment.system == System::PbLib {
                //String::from(" (PBLib)")
                format!(" (PBLib \\texttt{{{:?}}})", experiment.int_encoding)
            } else {
                String::from(" ")
            },
            lbl,
        );
        todo!("linestyles");
        // (lbl, 0)
    } else {
        (lbl, linestyle)
    }
}

pub struct Mkplot {
    pub title: String,
    pub plot_type: PlotType,
    pub x_label: String,
    pub y_label: String,
    pub save_to: String,
    pub xys: Vec<MkplotConfig>,
    pub log: bool,
    pub loc: String,
}

pub struct MkplotConfig {
    pub prog_alias: String,
    pub program: String,
    pub linestyle: usize,
    pub xy: Vec<(String, Option<f32>)>,
    pub skip_min_max: bool,
    pub path: PathBuf,
}

impl MkplotConfig {
    pub fn scm(
        experiment: &Experiment,
        xy: Vec<(String, Option<f32>)>,
        path: PathBuf,
        skip_min_max: bool,
    ) -> Self {
        let prog_alias = match &experiment {
            Experiment {
                system: System::MiniZinc,
                ..
            } => String::from("\\texttt{{picat}}"),
            Experiment {
                model_config: ModelConfig { scm, .. },
                ..
            } => match scm {
                Scm::Add => String::from("\\texttt{{min-a}}"),
                Scm::Rca => String::from("\\texttt{{min-k}}"),
                Scm::Pow => String::from("\\texttt{{base}}"),
                Scm::Dnf => String::from("\\texttt{{espresso}}"),
            },
        };
        let linestyle = match &experiment {
            Experiment {
                system: System::Pbc,
                model_config: ModelConfig { scm: Scm::Add, .. },
                ..
            } => 0,
            Experiment {
                system: System::Pbc,
                model_config: ModelConfig { scm: Scm::Rca, .. },
                ..
            } => 1,
            Experiment {
                system: System::Pbc,
                model_config: ModelConfig { scm: Scm::Pow, .. },
                ..
            } => 2,
            Experiment {
                system: System::Pbc,
                model_config: ModelConfig { scm: Scm::Dnf, .. },
                ..
            } => 3,
            Experiment {
                system: System::MiniZinc,
                ..
            } => 4,
            _ => {
                println!("WARNING: No linestyle set for {experiment:?}");
                6
            }
        };

        let program = format!("{}", experiment);
        Self {
            prog_alias,
            program,
            linestyle,
            xy,
            path,
            skip_min_max,
        }
    }
}

impl Mkplot {
    pub fn scm_static(xys: &[(Scm, Vec<(u32, (f32, f32, f32))>)], typ: usize) -> Self {
        let lbl = String::from(match typ {
            0 => "Variables",
            1 => "Clauses",
            2 => "Literals",
            _ => unreachable!(),
        });
        Self {
            title: format!("Static analysis ({})", lbl.clone().to_lowercase()),
            loc: String::from("lower right"),
            plot_type: PlotType::Instance,
            x_label: String::from("Bit width [\\#bits]"),
            y_label: lbl.clone(),
            save_to: format!("statics-{}", lbl.clone().to_lowercase()),
            xys: xys
                .iter()
                .map(|(scm, xy)| {
                    let experiment = Experiment {
                        system: System::Pbc,
                        model_config: ModelConfig {
                            scm: scm.clone(),
                            ..ModelConfig::default()
                        },
                        ..Experiment::default()
                    };
                    MkplotConfig::scm(
                        &experiment,
                        xy.iter()
                            .map(|(b, statics)| {
                                (
                                    format!("{b}"),
                                    Some(match typ {
                                        0 => statics.0,
                                        1 => statics.1,
                                        2 => statics.2,
                                        _ => unreachable!(),
                                    }),
                                )
                            })
                            .collect(),
                        PathBuf::from(format!("{}-statics-{lbl}.json", experiment)),
                        false,
                    )
                })
                .collect(),
            log: true,
        }
    }
}

const PBC_PB_ENCS: [PbEncoding; 3] = [PbEncoding::Gt, PbEncoding::Swc, PbEncoding::Bdd];

fn pbc_filter_experiments(experiment: &Experiment, pb_encoding: &PbEncoding) -> bool {
    // select just this pb_encoding
    ((experiment.system == System::Pbc || experiment.system == System::SavileRow)
        && experiment.pb_encoding == *pb_encoding)
        || experiment.system == System::Scop
        || (experiment.system == System::SavileRow
            && !PBC_PB_ENCS.contains(&experiment.pb_encoding))
}
