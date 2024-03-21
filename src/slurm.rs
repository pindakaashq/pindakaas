use crate::cli::Problem;
use crate::BufWriter;
use crate::File;
use crate::PathBuf;
use crate::{
    cli::{Nodelist, System},
    Experiment, Run,
    Run::Slurm,
};
use itertools::iproduct;

use itertools::Itertools;
use pindakaas::Scm;
use serde_json::to_writer_pretty;
use std::fs;
use std::io::Write;
use std::process::Command;

const ENVS: &[(&str, &str)] = &[("IPASIR", "./bin/cadical/build/libcadical.a")];

#[allow(clippy::identity_op)]
pub fn cmd(cmd: &str, envs: &[(&str, &str)]) -> String {
    print!("{}: ", cmd);
    match cmd.split_whitespace().collect::<Vec<_>>().as_slice() {
        [c, args @ ..] => {
            let output = Command::new(c)
                .args(args)
                .envs(envs.iter().cloned())
                .output()
                .unwrap();
            if output.status.success() {
                let out = String::from_utf8(output.stdout).unwrap();
                print!("{}", out);
                out
            } else {
                let err = String::from_utf8(output.stderr).unwrap();
                panic!("{}\n", err);
            }
        }
        _ => panic!(),
    }
}

pub fn slurm(run: Run) -> Result<(), String> {
    match run.clone() {
        Slurm {
            name: job_name,
            enc_timeout,
            solver_timeout,
            grace_timeout,
            nodelist,
            build,
            ..
        } => {
            if build {
                cmd("./build.sh", &[]);
            }

            let (dirs, runs) = do_setup(run);
            let time = enc_timeout + solver_timeout;

            println!(
                "MAX DUR: {} * {} = {}mins",
                runs.len(),
                time,
                runs.len() * (time / 60.0).ceil() as usize
            );

            // Write to experiments a bunch of load instructions / pipeline
            if matches!(nodelist, Nodelist::Setup) {
                return Ok(());
            } else if matches!(nodelist, Nodelist::Local) {
                const INTERMEDIATE_ANALYSES: bool = false;
                let n = runs.len();
                for (i, r) in runs.into_iter().enumerate() {
                    println!("Run #{} of {n}", i + 1);
                    crate::run(Run::Load { r }).unwrap_or_else(|err| println!("ERROR: {err}"));

                    if INTERMEDIATE_ANALYSES {
                        crate::run(Run::Analyze {
                            paths: vec![dirs.clone().root],
                            check: false,
                            plot: false,
                            y_log: false,
                            vbs: false,
                            scatter: false,
                            max_seed: None,
                            save_to: Some(dirs.clone().root),
                            fmt: String::from("png"),
                        })
                        .unwrap();
                    }
                }

                crate::run(Run::Analyze {
                    paths: vec![dirs.clone().root],
                    check: true,
                    plot: false,
                    y_log: false,
                    vbs: false,
                    scatter: false,
                    max_seed: None,
                    save_to: Some(dirs.root),
                    fmt: String::from("png"),
                })
                .unwrap();
            } else {
                let (nodelist, mem_gb) = nodelist.pars();
                let output = dirs.output.to_str().unwrap();
                let array_n = runs.len();
                let time_sec = time + grace_timeout;
                let out = cmd(&format!("sbatch --job-name={job_name} --output={output}/%a.out --array=1-{array_n} --time=0-00:00:{time_sec} --mem={mem_gb}gb {nodelist} ./batch.sh {}", dirs.runs.display()), &[]);
                let job_id = match_job_id(&out).unwrap();
                cmd(&format!("sbatch --dependency=afterany:{job_id} --job-name={job_name}-after --output={output}/after.out --time=0-00:15:00 --mem=4gb {nodelist} ./after.sh {}", dirs.stats.display()), &[]);
            }

            Ok(())
        }
        _ => unreachable!(),
    }
}

fn make_dir(dir: &str, mut parent: PathBuf) -> PathBuf {
    parent.push(dir);
    let mut builder = fs::DirBuilder::new();
    builder.recursive(true);
    builder.create(&parent).unwrap();
    parent
}

#[derive(Clone)]
struct Dirs {
    root: PathBuf,
    runs: PathBuf,
    lps: PathBuf,
    stats: PathBuf,
    output: PathBuf,
    aux: PathBuf,
    plots: PathBuf,
    slurm: PathBuf,
}

impl Dirs {
    pub fn new(name: &str) -> Self {
        let dir = make_dir(&name, PathBuf::from("./experiments"));

        assert!(dir.starts_with("./experiments"));
        fs::remove_dir_all(&dir).unwrap();
        let lps = make_dir("lps", dir.clone());
        let runs = make_dir("runs", dir.clone());
        let stats = make_dir("stats", dir.clone());
        let output = make_dir("output", dir.clone());
        let aux = make_dir("aux", dir.clone());
        let plots = make_dir("plots", dir.clone());
        make_dir("stats/encodes", dir.clone());
        make_dir("stats/solves", dir.clone());
        make_dir("jsons", dir.clone());

        let root = dir.clone();
        let mut slurm = dir;
        slurm.push("slurm.json");
        Self {
            root,
            runs,
            lps,
            stats,
            output,
            plots,
            aux,
            slurm,
        }
    }
}

fn do_setup(run: Run) -> (Dirs, Vec<PathBuf>) {
    match run.clone() {
        Slurm {
            name,
            seeds,
            enc_timeout,
            solver_timeout,
            experiments,
            problems,
            sat_cmd,
            check,
            nodelist,
            ..
        } => {
            let dirs = Dirs::new(&name);
            to_writer_pretty(BufWriter::new(File::create(&dirs.slurm).unwrap()), &run).unwrap();

            let instances = problems
                .iter()
                .flat_map(|problem| problem.clone().into_instances(dirs.lps.clone()))
                .collect::<Vec<_>>();

            const WRITE_RUN_TEX: bool = true;
            if WRITE_RUN_TEX {
                let mut tex = dirs.root.clone();
                tex.push("run.tex");
                let mut tex = File::create(tex).unwrap();

                let (_, mem_gb) = nodelist.pars();
                writeln!(
                    tex,
                    "
\\newcommand{{\\mbkpTimeoutP}}{{{solver_timeout}\\xspace}}
\\newcommand{{\\mbkpMemGbP}}{{{mem_gb}\\xspace}}
"
                )
                .unwrap();

                let mbkp = problems
                    .iter()
                    .filter(|problem| matches!(problem, Problem::Mbkp { .. }))
                    .last();

                if let Some(Problem::Mbkp {
                    n_,
                    m_,
                    q_,
                    s_,
                    seed,
                    ..
                }) = mbkp
                {
                    let b_ = mbkp.unwrap().mbkp_bit_width();

                    writeln!(
                        tex,
                        "
\\newcommand{{\\mbkpNP}}{{{n_}\\xspace}}
\\newcommand{{\\mbkpBP}}{{{b_}\\xspace}}
\\newcommand{{\\mbkpMP}}{{{m_}\\xspace}}
\\newcommand{{\\mbkpQP}}{{{q_}\\xspace}}
\\newcommand{{\\mbkpSP}}{{{s_}\\xspace}}
\\newcommand{{\\mbkpCP}}{{{seed}\\xspace}}
                        "
                    )
                    .unwrap();
                }
            }

            let experiments = experiments
                .into_iter()
                .filter(|experiments| !experiments.skip)
                .flat_map(|experiments| {
                    iproduct!(
                        experiments.int_encodings,
                        experiments.pb_encodings,
                        experiments.con_encodings,
                        experiments.add_consistencies,
                        experiments.cutoffs,
                        experiments.sort_same_coefficientss,
                        experiments.systems,
                        experiments.split_eqs,
                        experiments.propagates,
                        experiments.scms
                    )
                })
                .map(
                    |(
                        int_encoding,
                        pb_encoding,
                        con_encoding,
                        add_consistency,
                        cutoff,
                        sort_same_coefficients,
                        system,
                        split_eq,
                        propagate,
                        scm,
                    )| {
                        Experiment::new(
                            int_encoding,
                            pb_encoding,
                            con_encoding,
                            system,
                            add_consistency,
                            sort_same_coefficients,
                            split_eq,
                            propagate,
                            cutoff,
                            match scm {
                                0 => Scm::Add,
                                1 => Scm::Rca,
                                2 => Scm::Pow,
                                3 => Scm::Dnf,
                                _ => panic!(),
                            },
                        )
                    },
                )
                .filter(|e| {
                    if let Err(err) = e.is_supported() {
                        if nodelist == Nodelist::Local {
                            println!("Exp {e} not supported because of {err}");
                        } else {
                            panic!("Exp {e} not supported because of {err}");
                        }
                        false
                    } else {
                        true
                    }
                })
                // .map(|e| e.support())
                // .unique_by(|e| Experiment {
                //     model_config: ModelConfig::default(),
                //     ..e.clone() // ignore model config
                // })
                // .filter(|e| {
                //     if let Err(err) = e.is_supported() {
                //         println!("Exp {e} not supported because of {err}");
                //         false
                //     } else {
                //         true
                //     }
                // })
                .collect::<Vec<_>>();

            assert!(!experiments.is_empty());
            assert!(experiments.iter().all_unique());

            let runs = iproduct!(instances, experiments, 1..=seeds).collect::<Vec<_>>();
            let n = runs.len();

            (
                dirs.clone(),
                runs.into_iter()
                    .enumerate()
                    .map(
                        |(
                            i,
                            (
                                instance,
                                Experiment {
                                    int_encoding,
                                    pb_encoding,
                                    con_encoding,
                                    add_consistency,
                                    sort_same_coefficients,
                                    system,
                                    split_eq,
                                    propagate,
                                    model_config,
                                },
                                solve_seed,
                            ),
                        )| {
                            let id = i + 1;
                            let file_name =
                                format!("{:0n$}", id, n = (n as f32 + 1.0).log10().ceil() as usize);

                            let mut stats = dirs.stats.clone();
                            stats.push(format!("{}.json", file_name));

                            let mut aux_out = dirs.aux.clone();
                            aux_out.push(file_name.clone());

                            let sat_cmd = if matches!(system, System::SavileRow) {
                                Some(String::from("./bin/cadical/build/cadical"))
                            } else {
                                sat_cmd.clone()
                            };
                            let run = Run::Encode {
                                instance: Some(instance),
                                int_encoding,
                                pb_encoding,
                                con_encoding,
                                add_consistency,
                                cutoff: model_config.cutoff,
                                sort_same_coefficients,
                                system,
                                split_eq,
                                propagate,
                                scm: model_config.scm,
                                sat_cmd,
                                solve_seed: Some(solve_seed),
                                enc_timeout: Some(enc_timeout),
                                solver_timeout: Some(solver_timeout),
                                check,
                                aux_out: Some(aux_out.to_path_buf()),
                                stats: Some(stats.to_path_buf()),
                            };

                            let mut run_file = dirs.runs.clone();
                            run_file.push(format!("{}.json", file_name));

                            to_writer_pretty(
                                BufWriter::new(File::create(&run_file).unwrap()),
                                &run,
                            )
                            .unwrap();
                            run_file
                        },
                    )
                    .collect(),
            )
        }
        _ => unreachable!(),
    }
}

fn default_if_empty<T: Default>(vals: Vec<T>) -> Vec<T> {
    if vals.is_empty() {
        vec![T::default()]
    } else {
        vals
    }
}

fn match_job_id(out: &str) -> Result<u32, std::num::ParseIntError> {
    out.matches(char::is_numeric)
        .collect::<Vec<_>>()
        .join("")
        .parse()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn pattern_match_job_id_test() {
        assert_eq!(match_job_id("Submitted batch job 932309\n"), Ok(932309));
        assert!(match_job_id("somethi else\n").is_err());
    }
}
