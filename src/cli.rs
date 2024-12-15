#![allow(unreachable_code)]
use crate::analyze::SHOW_EXTS;
use crate::formula::{EncodeErr, Seed};
use crate::{encode_bkp, formula::C, generate_mbkp, Status};
use crate::{generate_mbssp, zero_pad};
use clap::{Parser, Subcommand, ValueEnum, ValueHint};
use itertools::iproduct;
use itertools::Itertools;
use pindakaas::integer::Assignment;
use pindakaas::integer::MapSol;
use pindakaas::integer::{Consistency, Decomposer, Format, Mix, Model, ModelConfig, Scm};
use pindakaas::solver::cadical::CadicalSol;
use pindakaas::solver::SolveResult;
use pindakaas::{CheckError, Cnf, Lit, Var};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::Display;
use std::ops::Add;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(name = "bkp")]
struct Arguments {
    #[command(subcommand)]
    run: Run,
}

pub fn parse() -> Run {
    let Arguments { run } = Arguments::parse();
    run
}

#[derive(Subcommand, Debug, Serialize, Deserialize, Clone)]
pub enum Run {
    Load {
        r: PathBuf,
    },
    Scm {
        #[arg(long)]
        bl: u32,
        #[arg(long)]
        bu: u32,
        #[arg(long)]
        cl: u32,
        #[arg(long)]
        cu: u32,
        #[arg(long, default_value = "png")]
        fmt: String,
    },
    Analyze {
        #[arg(value_hint(ValueHint::FilePath))]
        paths: Vec<PathBuf>,
        #[arg(long)]
        check: bool,
        #[arg(long)]
        filter_trivial: bool,
        #[arg(long)]
        plot: bool,
        #[arg(long)]
        table: bool,
        #[arg(long)]
        y_log: bool,
        #[arg(long, default_value_t = false)]
        vbs: bool,
        #[arg(long, default_value_t = false)]
        scatter: bool,
        #[arg(long)]
        max_seed: Option<Seed>,
        #[arg(long)]
        save_to: Option<PathBuf>,
        #[arg(long, default_value = "png")]
        fmt: String,
    },
    #[clap(skip)]
    Slurm {
        name: String,
        seeds: usize,

        build: bool,

        enc_timeout: f32,
        solver_timeout: f32,
        grace_timeout: f32,

        /// Memory in Gb (else `MaxMemPerNode` is used)
        mem: Option<f32>,

        nodelist: Nodelist,

        experiments: Vec<PathBuf>,

        check: bool,
        problems: Vec<Problem>,
    },
    #[clap(skip)]
    Generate {
        problem: Problem,
    },
    #[clap(skip)]
    Encode {
        instance: Option<Instance>,
        experiment: Experiment,

        aux_out: Option<PathBuf>,
        solve_seed: Option<usize>,

        enc_timeout: Option<f32>,
        solver_timeout: Option<f32>,
        mem: Option<f32>,
        stats: Option<PathBuf>,
        check: bool,
    },
    #[clap(skip)]
    Solve {
        path: PathBuf,
    },
}

impl Display for Run {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Run::Slurm { name, .. } => write!(f, "Job {name}"),
            Run::Encode {
                experiment,
                instance,
                ..
            } => write!(f, "Encode {}:{:?}", experiment, instance),
            _ => todo!(),
        }
    }
}

#[derive(
    Debug, Default, ValueEnum, Ord, PartialOrd, PartialEq, Eq, Hash, Deserialize, Clone, Serialize,
)]
pub enum System {
    #[default]
    Pbc,
    SavileRow,
    SavileRowBasic,
    Scop,
    MiniZinc,
    Abio,
    PbLib,
}

impl System {
    pub fn int_encodings(&self) -> &[IntEncoding] {
        pub const INT_ENCODINGS: &[IntEncoding] = &[
            // IntEncoding::Dir,
            IntEncoding::Ord,
            IntEncoding::Bin,
        ];
        match self {
            System::Pbc | System::PbLib | System::MiniZinc => INT_ENCODINGS,
            System::SavileRow | System::SavileRowBasic | System::Abio | System::Scop => {
                &[IntEncoding::Dir]
            }
        }
    }

    pub fn pb_encodings(&self) -> &[PbEncoding] {
        match self {
            System::Pbc => &[
                PbEncoding::Gt,
                // PbEncoding::Swc,
                PbEncoding::Bdd,
                PbEncoding::Adder,
            ],
            System::SavileRow | System::SavileRowBasic => &[
                PbEncoding::Gt,
                PbEncoding::Swc,
                PbEncoding::Bdd,
                PbEncoding::Gpw,
                PbEncoding::Tree,
                PbEncoding::Gmto,
            ],
            System::MiniZinc | System::Abio => &[PbEncoding::Gt],
            System::PbLib => &[
                PbEncoding::Swc,
                PbEncoding::Bdd,
                PbEncoding::Adder,
                PbEncoding::Gpw,
                PbEncoding::SortingNetwork,
                PbEncoding::BinaryMerger,
            ],
            System::Scop => &[PbEncoding::Bdd],
        }
    }

    pub fn con_encodings(&self) -> &[ConEncoding] {
        match self {
            System::Pbc => &[ConEncoding::Ignore, ConEncoding::Include],
            System::SavileRow
            | System::SavileRowBasic
            | System::MiniZinc
            | System::Abio
            | System::Scop => &[ConEncoding::Include],
            System::PbLib => &[ConEncoding::Ignore],
        }
    }

    pub fn add_consistencies(&self) -> &[bool] {
        match self {
            System::Pbc => &[false, true],
            System::SavileRow
            | System::SavileRowBasic
            | System::MiniZinc
            | System::Abio
            | System::Scop
            | System::PbLib => &[false],
        }
    }

    pub fn cutoffs(&self) -> &[Option<C>] {
        match self {
            System::Pbc => &[None, Some(0)],
            System::SavileRow
            | System::SavileRowBasic
            | System::MiniZinc
            | System::Abio
            | System::Scop
            | System::PbLib => &[None],
        }
    }

    pub fn split_eqs(&self) -> &[bool] {
        match self {
            System::Pbc => &[false, true],
            System::SavileRow
            | System::SavileRowBasic
            | System::MiniZinc
            | System::Abio
            | System::Scop
            | System::PbLib => &[false],
        }
    }

    pub fn propagates(&self) -> &[Consistency] {
        pub const CONSISTENCIES: &[Consistency] = &[Consistency::Bounds, Consistency::None];
        match self {
            System::Pbc => CONSISTENCIES,
            System::SavileRow
            | System::SavileRowBasic
            | System::MiniZinc
            | System::Abio
            | System::Scop
            | System::PbLib => &[Consistency::None],
        }
    }
}

#[derive(ValueEnum, Clone, Debug, Deserialize, Serialize, Hash, Eq, PartialEq)]
pub enum Nodelist {
    Critical,
    Extras,
    Local,
    Setup,
}

impl Nodelist {
    pub fn to_arg(&self) -> &str {
        match self {
            Nodelist::Critical => "--nodelist=critical001",
            Nodelist::Extras => "--exclude=critical001",
            _ => "",
        }
    }
    pub fn decide_mem(&self) -> f32 {
        match self {
            Nodelist::Critical => 8.0,
            Nodelist::Extras => 3.0,
            _ => -1.0, // TODO ?
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Problem {
    Soh {
        // number of int vars
        ns: Vec<usize>,
        // domain size
        ds: Vec<usize>,
    },
    Mbssp {
        /// upper bound of variables
        b: C,
        /// number of equality constraints (WARNING: n/m reversed with MBKP)
        n: usize,
        /// number of terms
        m: usize,
        /// max coefficient
        q: C,
        /// number of instances
        instances: usize,
    },
    Mmkp {
        /// number of PB constraints
        k_: usize,
        /// number of AMO constraints
        n_: usize,
        /// variable domain (=number of Boolean vars in each AMO constraint)
        m_: usize,
        /// weight domain
        q_: usize,
        /// aka instance
        family: u32,
        /// number of instance
        s_: u32,
        /// seed
        seed: Seed,
    },

    Mbkp {
        /// bound on number of items of each type
        bound: C,
        /// number of item types
        n_: usize,
        /// dimensions
        m_: usize,
        /// weight/profit domain
        q_: C,
        /// family/instance
        family: usize,
        /// number of instances
        s_: usize,
        /// seed (number of coefficient sets)
        seed: usize,
        /// scale lower
        fl: String,
        /// scale upper
        fu: Option<String>,

        skip_obj: bool,
    },

    Pbp {
        /// path to file(s)
        path: PathBuf,
        /// Limit to first k files
        limit: Option<usize>,
        /// Limit to first k files
        grep: Option<String>,
    },

    Str {
        lp: String,
    },

    Solve {
        /// path to Pseudo-Boolean Problem (pbp) file
        path: PathBuf,
        keep_file: bool,
        solve_seed: usize,
    },
}

const MBKP_S_BNDS: (f32, f32) = (0.25, 0.75);

impl Display for Problem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Problem::Mbssp {
                n,
                m,
                b,
                q,
                instances,
            } => write!(f, "mbssp_{n}_{m}_{b}_{q}_{instances}"),
            Problem::Mbkp {
                n_,
                bound,
                m_,
                q_,
                family,
                s_,
                seed,
                skip_obj: _,
                fl,
                fu,
            } => write!(
                f,
                "mbkp_{n_}_{bound}_{m_}_{q_}_{family}_{s_}_{seed}_{fl}_{}",
                fu.clone()
                    .unwrap_or_else(|| (1.0 - fl.parse::<f32>().unwrap()).to_string())
            ),
            Problem::Pbp { path, limit, grep } => {
                write!(
                    f,
                    "[{}] {} {}",
                    limit.unwrap_or(0),
                    grep.as_ref().unwrap_or(&String::from("*")),
                    path.to_str().unwrap().replace("./instances/", "")
                )
            }
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub struct Instance {
    pub problem: Problem,
    pub i: usize,
    pub lp: PathBuf,
}

impl Problem {
    pub fn mbkp_bit_width(&self) -> C {
        match self {
            Problem::Mbkp { bound, .. } => ((*bound as f32 + 1.0).log2()) as C,
            _ => unreachable!(),
        }
    }
    pub fn to_problem_label(&self) -> String {
        match self {
            Problem::Mbssp { n, m, b, q, .. } => {
                format!("$({m}, {b}, {n}, {q})$")
            }
            Problem::Mbkp {
                n_,
                bound,
                m_,
                q_,
                skip_obj: _,
                ..
            } => format!("$({n_}, {bound}, {m_}, {q_})$"),
            //} => format!("\\mbkpN={n_}, \\mbkpB={bound}, \\mbkpM={m_}, \\mbkpQ={q_}, \\mbkpS={s_}, \\mbkpC={seed}"),
            Problem::Pbp { path, .. } => {
                format!("LP: {}", path.display().to_string().replace("_", "/"))
            }
            _ => format!("{self:?}"),
        }
    }
    pub fn to_family_and_seed(&self, i: usize) -> (usize, usize) {
        if let Problem::Mbkp {
            s_: families, seed, ..
        } = self
        {
            let i = i - 1;
            ((i / families), (i % seed))
        } else {
            panic!()
        }
    }

    pub fn count_instances(&self) -> usize {
        match self {
            Problem::Mbkp { s_, seed, .. } => *s_ * *seed,
            Problem::Mbssp { instances, .. } => *instances,
            Problem::Pbp { .. } => self.instances(PathBuf::new()).len(),
            _ => todo!(),
        }
    }
    pub fn instances(&self, path: PathBuf) -> Vec<Instance> {
        match self.clone() {
            // Problem::Soh { ns, ds } => iproduct!(ns, ds)
            //     .map(|(n, d)| {
            //         let lp = dir.join(PathBuf::from(format!("{n}_{d}.lp")));
            //         Ilp::from_soh(n, d).to_file(lp.clone()).unwrap();
            //         lp
            //     })
            //     .collect(),
            Problem::Mbkp {
                n_,
                bound,
                m_,
                q_,
                s_: families,
                seed,
                fl,
                fu,
                ..
            } => {
                let fl = fl.parse().unwrap();
                let fu = fu
                    .clone()
                    .map(|fu| fu.parse().unwrap())
                    .unwrap_or_else(|| (1.0 - fl));
                let scale = Some((fl, fu));
                let prob = self.clone(); // TODO clean up clones..
                (0..families)
                    .flat_map(move |family| {
                        let path = path.clone();
                        let _prob = prob.clone();
                        (1..=seed).map(move |seed_i| {
                            let lp = path.clone().join(PathBuf::from(format!(
                                "{}_{}.lp",
                                zero_pad(seed_i, seed),
                                zero_pad(family, families)
                            )));

                            let model =
                                generate_mbkp(n_, bound, m_, q_, family, families, seed_i, scale);

                            std::fs::write(lp.clone(), model.to_text(Format::Lp)).unwrap();
                            lp
                        })
                    })
                    .collect()
            }
            #[allow(unused_variables)]
            Problem::Mbssp {
                n,
                m,
                b,
                q,
                instances,
            } => (1..=instances)
                .map(|i| {
                    let lp = path
                        .clone()
                        .join(PathBuf::from(format!("{}.lp", zero_pad(i, instances),)));

                    let model = generate_mbssp(n, m, b, q, i as Seed);

                    std::fs::write(lp.clone(), model.to_text(Format::Lp)).unwrap();
                    lp
                })
                .collect(),
            Problem::Pbp { path, grep, limit } => {
                let pbps = if path.is_dir() {
                    std::fs::read_dir(path)
                        .unwrap()
                        .map(|f| f.unwrap().path())
                        .sorted()
                        .collect_vec()
                } else if path.extension().unwrap().to_str().unwrap() == "txt" {
                    let file = std::fs::read_to_string(path).unwrap();
                    file.lines()
                        .filter(|l| !l.starts_with('#'))
                        .map(PathBuf::from)
                        .collect_vec()
                } else {
                    vec![path]
                };

                let n = pbps.len();
                pbps.into_iter()
                    .filter(|p| {
                        grep.as_ref()
                            .map(|g| p.to_str().unwrap().contains(g))
                            .unwrap_or(true)
                    })
                    .take(limit.unwrap_or(n))
                    // TODO this had an analysis step to sort by estimated difficulty / size
                    .collect_vec()
            }
            #[allow(unused_variables)]
            Problem::Str { lp } => {
                todo!();
                // let p = dir.join(PathBuf::from("problem.lp".to_string()));
                // std::fs::write(p.clone(), lp).unwrap();
                // vec![p]
            }
            x => unimplemented!("{x:?}"),
        }
        .into_iter()
        .enumerate()
        .map(|(i, lp)| Instance {
            problem: self.clone(),
            i: i + 1,
            lp,
        })
        .collect()
    }
}

#[derive(
    Debug, Default, ValueEnum, Ord, PartialOrd, PartialEq, Eq, Hash, Deserialize, Clone, Serialize,
)]
pub enum IntEncoding {
    Dir,
    #[default]
    Ord,
    Bin,
}

#[derive(
    Debug, Default, ValueEnum, Ord, PartialOrd, PartialEq, Eq, Hash, Deserialize, Clone, Serialize,
)]
pub enum PbEncoding {
    #[default]
    Gt,
    Swc,
    Bdd,
    Adder,
    Gpw,
    Tree,
    Gmto,
    SortingNetwork,
    BinaryMerger,
}
#[derive(
    Debug, Default, ValueEnum, Clone, Deserialize, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize,
)]
pub enum ConEncoding {
    #[default]
    Include,
    Ignore,
}

pub const SYSTEMS: &[System] = &[
    System::Pbc,
    System::SavileRow,
    System::Scop,
    // System::PbLib,
    // TODO System::MiniZinc
];

// TODO add Option to clear up json?
#[derive(Debug, Default, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ExperimentGen {
    pub int_encodings: Vec<IntEncoding>,
    pub pb_encodings: Vec<PbEncoding>,
    pub con_encodings: Vec<ConEncoding>,
    pub add_consistencies: Vec<bool>,
    pub cutoffs: Vec<Mix>,
    pub systems: Vec<System>,
    pub split_eqs: Vec<bool>,
    pub propagates: Vec<Consistency>,
    pub scms: Vec<Scm>,
    pub equalize_ternariess: Vec<bool>,
    pub skip: bool,
}

#[derive(Default, Debug, Clone, Deserialize, PartialEq, Eq, Hash, Ord, PartialOrd, Serialize)]
pub struct Experiment {
    pub system: System,
    pub pb_encoding: PbEncoding,
    pub int_encoding: IntEncoding,
    pub con_encoding: ConEncoding,
    pub split_eq: bool,
    pub model_config: ModelConfig,
}

impl Experiment {
    pub fn new(
        int_encoding: IntEncoding,
        pb_encoding: PbEncoding,
        con_encoding: ConEncoding,
        system: System,
        split_eq: bool,
        model_config: ModelConfig,
    ) -> Self {
        Self {
            int_encoding,
            pb_encoding,
            con_encoding,
            system,
            split_eq,
            model_config,
        }
    }

    pub fn scop(cutoff: Mix) -> Self {
        Experiment {
            int_encoding: IntEncoding::Dir,
            pb_encoding: PbEncoding::Bdd,
            con_encoding: ConEncoding::Include,
            system: System::Scop,
            model_config: ModelConfig {
                cutoff,
                ..ModelConfig::default()
            },
            ..Experiment::default()
        }
    }
    pub fn savile_row(pb_encoding: PbEncoding) -> Self {
        Experiment {
            int_encoding: IntEncoding::Dir,
            pb_encoding,
            con_encoding: ConEncoding::Include,
            system: System::SavileRow,
            model_config: ModelConfig::default(),
            ..Experiment::default()
        }
    }
    pub fn picat() -> Self {
        Experiment {
            int_encoding: IntEncoding::Dir,
            pb_encoding: PbEncoding::Gt,
            con_encoding: ConEncoding::Include,
            system: System::MiniZinc,
            model_config: ModelConfig::default(),
            ..Experiment::default()
        }

        // {
        //             cutoff: None,
        //             split_eq: false,
        //             propagate: false,
        //             scm: 0,
        //             equalize_ternaries: true,
        //             }
    }

    pub fn support(self) -> Self {
        Experiment {
            int_encoding: self
                .system
                .int_encodings()
                .contains(&self.int_encoding)
                .then_some(self.int_encoding)
                .unwrap_or_else(|| self.system.int_encodings().first().unwrap().clone()),
            pb_encoding: self
                .system
                .pb_encodings()
                .contains(&self.pb_encoding)
                .then_some(self.pb_encoding)
                .unwrap_or_else(|| self.system.pb_encodings().first().unwrap().clone()),
            con_encoding: self
                .system
                .con_encodings()
                .contains(&self.con_encoding)
                .then_some(self.con_encoding)
                .unwrap_or_else(|| self.system.con_encodings().first().unwrap().clone()),
            model_config: ModelConfig {
                add_consistency: self
                    .system
                    .add_consistencies()
                    .contains(&self.model_config.add_consistency)
                    .then_some(self.model_config.add_consistency)
                    .unwrap_or_else(|| *self.system.add_consistencies().first().unwrap()),
                propagate: self
                    .system
                    .propagates()
                    .contains(&self.model_config.propagate)
                    .then_some(self.model_config.propagate)
                    .unwrap_or_else(|| *self.system.propagates().first().unwrap()),
                ..Default::default()
            },
            split_eq: self
                .system
                .split_eqs()
                .contains(&self.split_eq)
                .then_some(self.split_eq)
                .unwrap_or_else(|| *self.system.split_eqs().first().unwrap()),
            // scm: self
            //     .system
            //     .scms()
            //     .contains(&self.scm)
            //     .then_some(self.scm)
            //     .unwrap_or_else(|| self.system.scms().first().unwrap().clone()),
            ..self
        }
    }
    pub fn is_supported(&self) -> Result<(), String> {
        if matches!(self.system, System::MiniZinc) {
            return Ok(());
        }
        [
            self.system
                .int_encodings()
                .contains(&self.int_encoding)
                .then_some(())
                .ok_or(format!("{:?}", self.int_encoding)),
            self.system
                .pb_encodings()
                .contains(&self.pb_encoding)
                .then_some(())
                .ok_or(format!("{:?}", self.pb_encoding)),
            self.system
                .con_encodings()
                .contains(&self.con_encoding)
                .then_some(())
                .ok_or(format!("{:?}", self.con_encoding)),
            self.system
                .add_consistencies()
                .contains(&self.model_config.add_consistency)
                .then_some(())
                .ok_or(format!("{:?}", self.model_config.add_consistency)),
        ]
        .into_iter()
        .collect()
    }

    pub(crate) fn display(&self, tex: bool) -> String {
        let cutoff_tex = match self.model_config.cutoff {
            Mix::Order => if tex { "\\mathbb{O}" } else { "Ord" }.to_owned(),
            // Mix::Order => if tex { "" } else { "Ord" }.to_owned(),
            Mix::Binary => if tex { "\\mathbb{B}" } else { "Bin" }.to_owned(),
            Mix::Mix(_) if self.system == System::Scop => "".to_owned(),
            Mix::Mix(c) => {
                if tex {
                    format!("\\cutoff{{{c}}}")
                } else {
                    format!("mix({c})")
                }
            }
        };

        let pb_enc = if tex {
            format!("\\text{{{}}}", self.pb_encoding)
        } else {
            format!("{}", self.pb_encoding)
        };

        // let tt = |s: &str| {
        //     if s.is_empty() || !tex {
        //         s.to_owned()
        //     } else {
        //         format!("\\texttt{{{s}}}")
        //     }
        // };

        match self.system {
            System::Pbc => format!(
                "${pb_enc}{}$",
                if self.con_encoding == ConEncoding::Ignore {
                    "".to_owned()
                } else if self.con_encoding == ConEncoding::Include && self.split_eq {
                    format!(" + {cutoff_tex}")
                // } else if !self.split_eq && self.model_config.cutoff == Mix::Order {
                } else {
                    format!(" + \\texttt{{eq}} + {cutoff_tex}")
                }
            ),
            System::Scop => format!(
                "{}{}",
                self.system,
                (!cutoff_tex.is_empty())
                    .then(|| format!(" ({cutoff_tex})"))
                    .unwrap_or_default()
            ),
            System::MiniZinc => "Picat-SAT (RCA)".to_owned(),
            System::SavileRow => format!("Savile Row ({pb_enc})"),
            _ => todo!(),
        }
    }

    pub(crate) fn to_alias(&self, problem: Option<&Problem>) -> (String, usize) {
        let is_mbkp = matches!(problem, Some(Problem::Mbkp { .. }) | None);
        let pb_encoding_lbl = format!("{}", self.pb_encoding);

        let cutoff_tex = format!(
            "\\texttt{{{}}}",
            match self.model_config.cutoff {
                Mix::Binary => "binary".to_string(),
                Mix::Mix(c) => format!("{c}"),
                Mix::Order => "order".to_string(),
            }
        );

        let (lbl, linestyle) = match self {
            Experiment {
                system: System::SavileRow,
                pb_encoding,
                ..
            } => (format!("Savile Row ({pb_encoding_lbl})"), if pb_encoding == &PbEncoding::Gmto { 7} else {6}),
            Experiment {
                system: System::Scop,
                ..
            // } => (format!("Fun-sCOP{}", if let (Some(0) | None) = cutoff { format!(" ({cutoff_tex})") } else {"".to_string()})), 8,
            } => (format!("{}", self), 8),
            Experiment {
                system: System::PbLib,
                ..
            } => (String::from("PBLib"), 9),
            Experiment {
                system: System::MiniZinc,
                ..
            } => (String::from("Picat-SAT"), 10),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                model_config: ModelConfig {cutoff: Mix::Mix(_) | Mix::Binary, ..},
                ..
            //} => 3,
            } => (format!("{pb_encoding_lbl} ({cutoff_tex})"), 5),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                model_config: ModelConfig {
                add_consistency: true,
                    cutoff: Mix::Order, ..},
                ..
            } => (format!("{pb_encoding_lbl} + \\ldots + \\texttt{{cons}}"), 4),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                model_config: ModelConfig {
                    propagate: Consistency::Bounds,
                    add_consistency: false,
                    cutoff: Mix::Order, ..},
                ..
            //} => 3,
            } if !is_mbkp =>  (format!("{pb_encoding_lbl} + \\ldots + \\texttt{{prop}}"), 3),
            Experiment {
                con_encoding: ConEncoding::Include,
                split_eq: false,
                model_config: ModelConfig {cutoff: Mix::Order, ..},
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
            let _lbl = format!(
                "{}{}{}{}{}{}{} ({})",
                format!("{:?}", self.pb_encoding).to_uppercase(),
                if self.con_encoding == ConEncoding::Include {
                    " + \\texttt{{int}}"
                } else {
                    " "
                },
                if !self.split_eq
                    && !is_mbkp
                    && !(matches!(self.system, System::SavileRow | System::SavileRowBasic))
                {
                    " + \\texttt{{eqs}}"
                } else {
                    " "
                },
                if self.model_config.propagate == Consistency::Bounds && !is_mbkp {
                    " + \\texttt{{prop}}"
                } else {
                    " "
                },
                if self.model_config.cutoff == Mix::Binary {
                    " + \\texttt{{bin}}"
                } else {
                    " "
                },
                if self.model_config.add_consistency {
                    " + \\texttt{{cons}}"
                } else {
                    " "
                },
                if self.system == System::SavileRow {
                    format!(" (SR \\texttt{{{:?}}})", self.int_encoding)
                } else if self.system == System::SavileRowBasic {
                    String::from(" (SavileRowBasic)")
                } else if self.system == System::PbLib {
                    //String::from(" (PBLib)")
                    format!(" (PBLib \\texttt{{{:?}}})", self.int_encoding)
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
}

impl TryFrom<PbEncoding> for Decomposer {
    type Error = ();

    fn try_from(value: PbEncoding) -> Result<Self, Self::Error> {
        match value {
            PbEncoding::Gt => Ok(Decomposer::Gt),
            PbEncoding::Swc => Ok(Decomposer::Swc),
            PbEncoding::Bdd => Ok(Decomposer::Bdd),
            PbEncoding::Adder => Ok(Decomposer::Rca),
            _ => Ok(Decomposer::Gt),
        }
    }
}
#[derive(Debug, Deserialize, Serialize, Default, Clone)]
pub struct EncodeRecord {
    pub instance: Option<Instance>,
    pub experiment: Option<Experiment>,
    pub statics: Option<StaticsRecord>,
    pub pb_statics: Option<PbStaticsRecord>,
    #[serde(skip_serializing, skip_deserializing)]
    pub principal: Option<Var>,
    pub time: Option<f32>,
    pub dimacs: Option<PathBuf>,
    // pub obj: Option<Obj<Lit, C>>,
}

// #[derive(Serialize, Deserialize)]
// #[serde(remote = "Lit")]
// struct LitDef {
//     secs: i64,
//     nanos: i32,
// }

#[derive(Debug, Deserialize, Serialize, Clone, Default, derive_more::Add, derive_more::Sum)]
pub struct StaticsRecord {
    pub vars: usize,
    pub cls: usize,
    pub lits: usize,
}

impl Display for StaticsRecord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}/{}/{}", self.vars, self.cls, self.lits)
    }
}

impl From<&Cnf> for StaticsRecord {
    fn from(cnf: &Cnf) -> Self {
        Self {
            vars: cnf.variables(),
            cls: cnf.clauses(),
            lits: cnf.literals(),
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, Default)]
pub struct PbStaticsRecord {
    pub lin_eqs: u32,
    pub lin_les: u32,
    pub card_eqs: u32,
    pub card_les: u32,
    pub amo_eqs: u32,
    pub amo_les: u32,
    pub trivs: u32,
}

#[derive(Debug, Default, Deserialize, Serialize, Clone, PartialEq)]
pub struct SolveRecord {
    pub status: Status,
    #[serde(skip_serializing, skip_deserializing)]
    pub solution: Option<MapSol>,
    pub assignment: Option<Assignment>,
    pub time: f32,
    pub cost: Option<C>,
    pub check: Option<Result<(), Vec<CheckError>>>,
}

impl SolveRecord {
    pub(crate) fn check(&self, model: &Model) -> Option<Result<(), Vec<CheckError>>> {
        match &self.status {
            Status::Sat | Status::Error(EncodeErr::Trivial(true)) => {
                self.assignment
                    .as_ref() // trivial for control does not necessarily have an assignment
                    .map(|a| model.check_assignment(a))
            }
            Status::Unsat
            | Status::Unknown
            | Status::Encoded
            | Status::Error(EncodeErr::Timeout | EncodeErr::Memory)
            | Status::Error(EncodeErr::Trivial(false)) => None,
            Status::Error(EncodeErr::Error(s)) => Some(Err(vec![CheckError::Fail(s.clone())])),
            Status::Opt => todo!(),
        }
    }
}

// impl From<SolveResult<CadicalSol<'_>>> for SolveRecord {
//     fn from(s: SolveResult<CadicalSol>) -> Self {
//         match s {
//             SolveResult::Satisfied(sol) => MapSol::new(
//             SolveResult::Unsatisfiable(_) => todo!(),
//             SolveResult::Unknown => todo!(),
//         }
//         Self {
//             // solution: MapSol,
//             status: Status::from(s),
//             // time: solve_timer.elapsed().as_secs_f32(),
//             ..SolveRecord::default()
//         }
//     }
// }

impl core::fmt::Display for SolveRecord {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "Got {} in {}s with check {:?}: {}",
            self.status,
            self.time,
            self.check,
            self.assignment
                .as_ref()
                .map(|s| format!("{s}"))
                .unwrap_or_default()
        )
    }
}

impl StaticsRecord {
    pub fn new(vars: usize, cls: usize, lits: usize) -> Self {
        Self { vars, cls, lits }
    }
}
