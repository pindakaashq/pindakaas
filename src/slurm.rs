use crate::cli::ExperimentGen;
use crate::cli::Problem;
use crate::formula::EncodeErr;
use crate::zero_pad;
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
use pindakaas::integer::Decomposer;
use pindakaas::integer::Format;
use pindakaas::integer::ModelConfig;
use pindakaas::integer::Scm;
use serde_json::to_writer_pretty;
use std::fs;
use std::fs::create_dir;
use std::io::BufRead;
use std::io::Write;
use std::process::Command;

const ENVS: &[(&str, &str)] = &[("IPASIR", "./bin/cadical/build/libcadical.a")];

#[allow(clippy::identity_op)]
pub fn cmd(
    cmd: &str,
    envs: &[(&str, &str)],
    timeout: Option<f32>,
) -> Result<(String, String), EncodeErr> {
    let cmd = timeout
        .map(|t| {
            let t = t.round() as u32;
            assert!(t > 0, "timeout too short");
            format!("timeout {t}")
        })
        .into_iter()
        .chain([cmd.to_string()])
        .join(" ");
    if let [c, args @ ..] = cmd.split_whitespace().collect_vec().as_slice() {
        println!("CMD {} {}", c, args.join(" "));
        let output = Command::new(c)
            .args(args)
            .envs(envs.iter().cloned())
            .output()
            .unwrap();
        let (out, err) = (
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(output.stderr).unwrap(),
        );

        let code = output.status.code().unwrap();
        #[cfg(debug_assertions)]
        println!("EXIT={code}\nSTDOUT:\n{out}\nSTDERR:\n{err}",);

        if code == 124 {
            Err(EncodeErr::Timeout)
        } else if out.contains("java.lang.OutOfMemoryError") // sometimes essence
            || err.contains("java.lang.OutOfMemoryError")
            || (err.contains("Out of Memory") && code == 1)
        // essence since 1.10.1
        {
            Err(EncodeErr::Memory)
        } else if output.status.success()
            || (out.contains("UNSUPPORTED") && cmd.contains("./bin/fun-scop/scop.jar"))
        {
            Ok((out, err))
        } else {
            Err(EncodeErr::Error(format!(
                "The command {cmd} failed with exit code {code}\nSTDOUT:\n{out}\nSTDERR:\n{err}",
            )))
        }
    } else {
        panic!()
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
            mem,
            ..
        } => {
            if build {
                cmd("./build.sh", &[], None).unwrap();
            }

            let (dirs, runs) = do_setup(run);
            assert!(!runs.is_empty());
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
                    println!("Run #{} of {n}: {r:?}", i + 1);
                    crate::run(Run::Load { r }).unwrap_or_else(|err| println!("ERROR: {err}"));

                    if INTERMEDIATE_ANALYSES {
                        crate::run(Run::Analyze {
                            paths: vec![dirs.clone().root],
                            check: true,
                            plot: false,
                            table: false,
                            y_log: false,
                            vbs: false,
                            scatter: false,
                            max_seed: None,
                            save_to: Some(dirs.root.clone()),
                            fmt: String::from("png"),
                            filter_trivial: false,
                        })
                        .unwrap();
                    }
                }

                crate::run(Run::Analyze {
                    paths: vec![dirs.clone().root],
                    check: true,
                    plot: false,
                    table: true,
                    y_log: false,
                    vbs: false,
                    scatter: false,
                    max_seed: None,
                    save_to: Some(dirs.root),
                    fmt: String::from("png"),
                    filter_trivial: false,
                })
                .unwrap();
            } else {
                let nodelist_arg = nodelist.to_arg();
                let output = dirs.output.to_str().unwrap();
                let array_n = runs.len();
                let time_sec = time + grace_timeout;
                let slurm_mem = mem
                    .map(|mem| {
                        format!("{}gb", mem + 1.0) // Grace memory for slurm
                                                   // const KIBIBYTE: f32 = 976563.0;
                                                   // let ulimit_mem = ((mem + 0.5) * KIBIBYTE).round(); // Slurm's grace memory contains memory for ulimit: GB to kibibytes + 0.5GB grace for ulimited program
                    })
                    .unwrap_or("MaxMemPerNode".to_owned());

                let runs_dir = dirs.runs.display();
                let (out,_) = cmd(&format!("sbatch --job-name={job_name} --output={output}/%a.out --array=1-{array_n} --time=0-00:00:{time_sec} --mem={slurm_mem} {nodelist_arg} ./batch.sh {runs_dir} --clean"), &[], None).unwrap();
                let job_id = match_job_id(&out)
                    .unwrap_or_else(|_| panic!("Could not match job id from slurm out:{out}"));
                cmd(&format!("sbatch --dependency=afterany:{job_id} --job-name={job_name}-after --output={output}/after.out --time=0-00:15:00 --mem=4gb {nodelist_arg} ./after.sh {}", dirs.stats.display()), &[], None).unwrap();
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
    tables: PathBuf,
}

impl Dirs {
    pub fn new(name: &str) -> Self {
        let dir = make_dir(name, PathBuf::from("./experiments"));

        assert!(dir.starts_with("./experiments"));
        fs::remove_dir_all(&dir).unwrap();
        let lps = make_dir("lps", dir.clone());
        let runs = make_dir("runs", dir.clone());
        let stats = make_dir("stats", dir.clone());
        let output = make_dir("output", dir.clone());
        let aux = make_dir("aux", dir.clone());
        let plots = make_dir("plots", dir.clone());
        let tables = make_dir("tables", dir.clone());
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
            tables,
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
            check,
            nodelist,
            mem,
            ..
        } => {
            let dirs = Dirs::new(&name);
            to_writer_pretty(BufWriter::new(File::create(&dirs.slurm).unwrap()), &run).unwrap();

            let instances = problems
                .iter()
                .enumerate()
                .flat_map(|(i, problem)| {
                    let dir = [dirs.lps.clone(), zero_pad(i + 1, problems.len()).into()]
                        .into_iter()
                        .collect();
                    create_dir(&dir).unwrap();
                    problem.clone().instances(dir)
                })
                .collect::<Vec<_>>();

            let experiments = experiments
                .into_iter()
                .flat_map(|p| {
                    std::fs::read_to_string(p.clone())
                        .map(|r| {
                            serde_json::from_str::<Vec<ExperimentGen>>(&r).unwrap_or_else(|e| {
                                panic!("Could not deserde {} because {e}", p.display())
                            })
                        })
                        .unwrap_or_default()
                })
                .filter(|experiments| !experiments.skip)
                .flat_map(|experiments| {
                    iproduct!(
                        experiments.int_encodings,
                        experiments.pb_encodings,
                        experiments.con_encodings,
                        experiments.add_consistencies,
                        experiments.cutoffs,
                        experiments.systems,
                        experiments.split_eqs,
                        experiments.propagates,
                        experiments.scms,
                        experiments.equalize_ternariess
                    )
                })
                .map(
                    |(
                        int_encoding,
                        pb_encoding,
                        con_encoding,
                        add_consistency,
                        cutoff,
                        system,
                        split_eq,
                        propagate,
                        scm,
                        equalize_ternaries,
                    )| {
                        Experiment {
                            system,
                            pb_encoding: pb_encoding.clone(),
                            int_encoding,
                            con_encoding,
                            split_eq,
                            model_config: ModelConfig {
                                add_consistency,
                                decomposer: Decomposer::try_from(pb_encoding).unwrap(),
                                cutoff,
                                propagate,
                                scm,
                                equalize_ternaries,
                                ..Default::default()
                            },
                        }
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
                    .map(|(i, (instance, experiment, solve_seed))| {
                        let id = i + 1;
                        let file_name =
                            format!("{:0n$}", id, n = (n as f32 + 1.0).log10().ceil() as usize);

                        let mut stats = dirs.stats.clone();
                        stats.push(format!("{}.json", file_name));

                        let mut aux_out = dirs.aux.clone();
                        aux_out.push(file_name.clone());

                        let run = Run::Encode {
                            instance: Some(instance),
                            experiment,
                            solve_seed: Some(solve_seed),
                            enc_timeout: Some(enc_timeout),
                            solver_timeout: Some(solver_timeout),
                            check,
                            aux_out: Some(aux_out.to_path_buf()),
                            stats: Some(stats.to_path_buf()),
                            mem,
                        };

                        let mut run_file = dirs.runs.clone();
                        run_file.push(format!("{}.json", file_name));

                        to_writer_pretty(BufWriter::new(File::create(&run_file).unwrap()), &run)
                            .unwrap();
                        run_file
                    })
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
