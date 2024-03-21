use crate::ilp::Ilp;

use crate::{
    formula::{Lit, C},
    Status,
};
use clap::{Parser, Subcommand, ValueEnum, ValueHint};
use itertools::iproduct;
use itertools::Itertools;
use pindakaas::{Cnf, Coefficient, Consistency, Decomposer, Format, Literal, ModelConfig, Scm};
use serde::{Deserialize, Serialize};
use std::fmt::Display;
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

#[derive(Subcommand, Debug, Deserialize, Serialize, Clone)]
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
        #[arg(long, default_value_t = true)]
        check: bool,
        #[arg(long)]
        plot: bool,
        #[arg(long)]
        y_log: bool,
        #[arg(long, default_value_t = false)]
        vbs: bool,
        #[arg(long, default_value_t = false)]
        scatter: bool,
        #[arg(long)]
        max_seed: Option<usize>,
        #[arg(long)]
        save_to: Option<PathBuf>,
        #[arg(long, default_value = "png")]
        fmt: String,
    },
    Slurm {
        #[arg(default_value = "dev")]
        name: String,
        #[arg(long, default_value_t = 1)]
        seeds: usize,

        #[arg(long)]
        build: bool,

        #[arg(long, default_value_t = 3.0*60.0)]
        enc_timeout: f32,

        #[arg(long, default_value_t = 5.0*60.0)]
        solver_timeout: f32,

        #[arg(long, default_value_t = 1.0*60.0)]
        grace_timeout: f32,

        #[arg(long, value_enum, default_value_t = crate::cli::Nodelist::Local)]
        nodelist: Nodelist,

        #[arg(long, value_parser = |_: &str| { Ok::<Vec<ExperimentGen>, String>(vec![]) })]
        experiments: Vec<ExperimentGen>,

        #[arg(long)]
        sat_cmd: Option<String>,

        #[arg(long)]
        check: bool,

        #[clap(skip)]
        problems: Vec<Problem>,
    },
    Generate {
        #[command(subcommand)]
        problem: Problem,
    },
    Encode {
        #[clap(skip)]
        instance: Option<Instance>,

        #[arg(value_enum)]
        int_encoding: IntEncoding,
        #[arg(value_enum)]
        pb_encoding: PbEncoding,
        #[arg(value_enum)]
        con_encoding: ConEncoding,
        #[arg(value_enum)]
        add_consistency: AddConsistency,
        #[arg(long)]
        cutoff: Option<C>,
        #[arg(long, default_value_t = 0)]
        sort_same_coefficients: usize,
        #[arg(value_enum)]
        system: System,
        #[arg(long)]
        split_eq: bool,
        #[arg(long)]
        propagate: bool,
        #[serde(with = "ScmDef")]
        #[clap(skip)]
        scm: Scm,

        #[clap(long)]
        aux_out: Option<PathBuf>,
        #[clap(long)]
        sat_cmd: Option<String>,
        #[clap(long)]
        solve_seed: Option<usize>,

        #[arg(long)]
        enc_timeout: Option<f32>,

        #[arg(long)]
        solver_timeout: Option<f32>,

        #[arg(long)]
        check: bool,

        #[arg(long)]
        stats: Option<PathBuf>,
    },

    // TODO
    // Sat {
    //     /// path to EncodeRecord (json) file
    //     #[arg(value_hint(ValueHint::FilePath))]
    //     path: PathBuf,
    // },
    Solve {
        #[arg(long)]
        path: PathBuf,
    },
}

#[derive(
    Debug, Default, ValueEnum, Ord, PartialOrd, PartialEq, Eq, Hash, Deserialize, Clone, Serialize,
)]
pub enum System {
    #[default]
    Pbc,
    SavileRow,
    SavileRowBasic,
    MiniZinc,
    Abio,
    PbLib,
    Scop,
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
                PbEncoding::Swc,
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

    pub fn add_consistencies(&self) -> &[AddConsistency] {
        match self {
            System::Pbc => &[AddConsistency::Skip, AddConsistency::Aux],
            System::SavileRow
            | System::SavileRowBasic
            | System::MiniZinc
            | System::Abio
            | System::Scop
            | System::PbLib => &[AddConsistency::Skip],
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

    pub fn propagates(&self) -> &[bool] {
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
}

#[derive(ValueEnum, Clone, Debug, Deserialize, Serialize, Hash, Eq, PartialEq)]
pub enum Nodelist {
    Critical,
    Extras,
    Local,
    Setup,
}
impl Nodelist {
    pub fn pars(&self) -> (&str, i32) {
        match self {
            Nodelist::Critical => ("--nodelist=critical001", 8),
            Nodelist::Extras => ("--exclude=critical001", 3),
            _ => ("", -1),
        }
    }
}

#[derive(
    Subcommand, Clone, Debug, Deserialize, Serialize, Hash, Eq, PartialEq, PartialOrd, Ord,
)]
pub enum Problem {
    Soh {
        // number of int vars
        ns: Vec<usize>,
        // domain size
        ds: Vec<usize>,
    },
    RandEqs {
        // number of equality constraints
        n: usize,
        // number of terms
        m: usize,
        // upper bound of variables
        b: usize,
        // max coefficient
        q: usize,
        // number of instances
        instances: usize,
    },
    Mmkp {
        /// number of PB constraints
        #[clap(short)]
        k_: usize,
        /// number of AMO constraints
        #[clap(short)]
        n_: usize,
        /// variable domain (=number of Boolean vars in each AMO constraint)
        #[clap(short)]
        m_: usize,
        /// weight domain
        #[clap(short)]
        q_: usize,
        /// aka instance
        #[clap(long)]
        family: u32,
        /// number of instance
        #[clap(short)]
        s_: u32,
        /// seed
        #[clap(long)]
        seed: u64,
    },

    Mbkp {
        /// number of item types
        #[clap(short)]
        n_: usize,
        /// bound on number of items of each type
        #[clap(short)]
        bound: usize,
        /// dimensions
        #[clap(short)]
        m_: usize,
        /// weight/profit domain
        #[clap(short)]
        q_: usize,
        /// family/instance
        #[clap(long)]
        family: u32,
        /// number of instances
        #[clap(short)]
        s_: u32,
        /// seed
        #[clap(long)]
        seed: u64,

        #[clap(long)]
        skip_obj: bool,
    },

    Pbp {
        /// path to file(s)
        #[arg(value_hint(ValueHint::FilePath))]
        path: PathBuf,
        /// Limit to first k files
        #[clap(long)]
        limit: Option<usize>,
        /// Limit to first k files
        #[clap(long)]
        grep: Option<String>,
    },

    Solve {
        /// path to Pseudo-Boolean Problem (pbp) file
        #[arg(value_hint(ValueHint::FilePath))]
        path: PathBuf,
        #[clap(long)]
        sat_cmd: PathBuf,
        #[clap(long, default_value_t = false)]
        keep_file: bool,
        #[clap(long, default_value_t = 0)]
        solve_seed: usize,
    },
}

const MBKP_S_BNDS: (f32, f32) = (0.25, 0.75);

impl Display for Problem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Problem::RandEqs {
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
            } => write!(f, "mbkp_{n_}_{bound}_{m_}_{q_}_{family}_{s_}_{seed}"),
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
            Problem::RandEqs { n, m, b, q, .. } => {
                format!("\\mbsspN={n}, \\mbsspB={b}, \\mbsspM={m}, \\mbsspQ={q}")
            }
            Problem::Mbkp {
                n_,
                bound,
                m_,
                q_,
                skip_obj: _,
                ..
            } => format!("\\mbkpN={n_}, \\mbkpB={bound}, \\mbkpM={m_}, \\mbkpQ={q_}"),
            //} => format!("\\mbkpN={n_}, \\mbkpB={bound}, \\mbkpM={m_}, \\mbkpQ={q_}, \\mbkpS={s_}, \\mbkpC={seed}"),
            _ => format!("{self:?}"),
        }
    }
    pub fn to_family_and_seed(&self, i: usize) -> (u32, u64) {
        if let Problem::Mbkp {
            s_: families, seed, ..
        } = self
        {
            let i = i - 1;
            ((i as u32 / families), (i as u64 % seed))
        } else {
            panic!()
        }
    }

    pub fn into_instances(self, dir: PathBuf) -> Vec<Instance> {
        match self.clone() {
            Problem::Soh { ns, ds } => iproduct!(ns, ds)
                .map(|(n, d)| {
                    let lp = dir.join(PathBuf::from(format!("{n}_{d}.lp")));
                    Ilp::from_soh(n, d).to_file(lp.clone()).unwrap();
                    lp
                })
                .collect(),
            Problem::Mbkp {
                n_,
                bound,
                m_,
                q_,
                s_: families,
                seed,
                skip_obj,
                ..
            } => (1..=families)
                .flat_map(|family| {
                    let dir = dir.clone();
                    (1..=seed).map(move |seed| {
                        let lp = dir.join(PathBuf::from(format!(
                            "{n_}_{bound}_{m_}_{q_}_{family}_{families}_{seed}_{}.lp",
                            if skip_obj { "sat" } else { "opt" }
                        )));
                        std::fs::write(
                            lp.clone(),
                            Ilp::from_mbkp(n_, bound, m_, q_, family, families, seed, skip_obj)
                                .to_text(Format::Lp),
                        )
                        .unwrap();
                        lp
                    })
                })
                .collect(),
            Problem::RandEqs {
                n,
                m,
                b,
                q,
                instances,
            } => (1..=instances)
                .map(|seed| {
                    let seed_zero_padded = format!(
                        "{:0n$}",
                        seed,
                        n = (instances as f32 + 1.0).log10().ceil() as usize
                    );

                    let lp = dir.join(PathBuf::from(format!(
                        "{n}_{m}_{b}_{q}_{seed_zero_padded}.lp"
                    )));
                    Ilp::from_rand_eqs(n, m, b, q, seed as u64)
                        .to_file(lp.clone())
                        .unwrap();
                    lp
                })
                .collect(),
            Problem::Pbp { path, grep, limit } => {
                if path.is_dir() {
                    std::fs::read_dir(path)
                        .unwrap()
                        .map(|f| f.unwrap().path())
                        .sorted()
                        .collect()
                } else if path.extension().unwrap().to_str().unwrap() == "txt" {
                    let file = std::fs::read_to_string(path).unwrap();
                    let n = file.lines().count();
                    file.lines()
                        .filter(|l| !l.starts_with('#'))
                        .map(PathBuf::from)
                        .filter(|p| {
                            grep.as_ref()
                                .map(|g| p.to_str().unwrap().contains(g))
                                .unwrap_or(true)
                        })
                        .enumerate()
                        .filter_map(|(i, l)| match Ilp::from_file(l.clone()) {
                            Ok(ilp) => {
                                let stats = ilp.analyze(true).ok()?;
                                // None
                                // (statics.lin_eqs > 0 || statics.lin_les > 0).then_some(l)
                                // Some(l)

                                // eprintln!("{i}/{n} {lin} {statics:?}");
                                let name = l.to_str().unwrap().trim();
                                eprintln!(
                                    "{}/{n} {name} lins={} max_k={} {:?}",
                                    i + 1,
                                    stats.0,
                                    stats.1,
                                    stats.2
                                );
                                (stats.0 > 0 && stats.1 > 10).then_some((i, l, stats))
                                // Some((i, lin, l, statics))
                            }
                            Err(e) => {
                                println!("Skipping {l:?} since {e}");
                                None
                            }
                        })
                        .sorted_by_key(|(_, _, (lins, _, _))| *lins)
                        .rev()
                        .take(limit.unwrap_or(n))
                        // .sorted()
                        .filter_map(|(i, l, stats)| {
                            let name = l.to_str().unwrap().trim();
                            eprintln!(
                                "{}/{n} {name} lins={} max_k={} {:?}",
                                i + 1,
                                stats.0,
                                stats.1,
                                stats.2
                            );
                            // None
                            Some(l)
                        })
                        .collect()
                } else {
                    vec![path]
                }
            }
            _ => unimplemented!(),
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

#[derive(
    Debug, Default, ValueEnum, Clone, Deserialize, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize,
)]

pub enum AddConsistency {
    Aux,
    #[default]
    Skip,
}

pub const SYSTEMS: &[System] = &[
    System::Pbc,
    System::SavileRow,
    System::Scop,
    // System::PbLib,
    // TODO System::MiniZinc
];

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ExperimentGen {
    pub int_encodings: Vec<IntEncoding>,
    pub pb_encodings: Vec<PbEncoding>,
    pub con_encodings: Vec<ConEncoding>,
    pub add_consistencies: Vec<AddConsistency>,
    pub cutoffs: Vec<Option<C>>,
    pub sort_same_coefficientss: Vec<usize>,
    pub systems: Vec<System>,
    pub split_eqs: Vec<bool>,
    pub propagates: Vec<bool>,
    pub scms: Vec<u32>,
    pub skip: bool,
}

#[derive(Default, Debug, Clone, Deserialize, PartialEq, Eq, Hash, Ord, PartialOrd, Serialize)]
pub struct Experiment {
    pub pb_encoding: PbEncoding,
    pub system: System,
    pub int_encoding: IntEncoding,
    pub con_encoding: ConEncoding,
    pub add_consistency: AddConsistency,
    pub sort_same_coefficients: usize,
    pub split_eq: bool,
    pub propagate: bool,
    #[serde(with = "ModelConfigDef")]
    pub model_config: ModelConfig<C>,
}

impl Experiment {
    pub fn new(
        int_encoding: IntEncoding,
        pb_encoding: PbEncoding,
        con_encoding: ConEncoding,
        system: System,
        add_consistency: AddConsistency,
        sort_same_coefficients: usize,
        split_eq: bool,
        propagate: bool,
        cutoff: Option<C>,
        scm: Scm,
    ) -> Self {
        let decomposer = Decomposer::try_from(pb_encoding.clone()).unwrap();
        let cutoff = if decomposer == Decomposer::Rca {
            Some(0)
        } else {
            cutoff.clone()
        };
        Self {
            int_encoding,
            pb_encoding,
            con_encoding,
            add_consistency: add_consistency.clone(),
            sort_same_coefficients,
            system,
            split_eq,
            propagate,
            model_config: ModelConfig {
                scm,
                cutoff,
                decomposer,
                add_consistency: add_consistency == AddConsistency::Aux,
                propagate: if propagate {
                    Consistency::Bounds
                } else {
                    Consistency::None
                },
            },
        }
    }
}

#[derive(
    Debug, Default, ValueEnum, Ord, PartialOrd, PartialEq, Eq, Hash, Deserialize, Clone, Serialize,
)]
#[serde(remote = "Scm")]
pub enum ScmDef {
    #[default]
    Add,
    Rca,
    Pow,
    Dnf,
    // Ord,
}

#[derive(
    Debug, Default, ValueEnum, Ord, PartialOrd, PartialEq, Eq, Hash, Clone, Serialize, Deserialize,
)]
#[serde(remote = "Decomposer")]
pub enum DecomposerDef {
    #[default]
    Bdd,
    Gt,
    Swc,
    Rca,
}

#[derive(
    Serialize, Deserialize, Copy, Debug, Default, Eq, Ord, PartialOrd, Hash, Clone, PartialEq,
)]
#[serde(remote = "Consistency")]
pub enum ConsistencyDef {
    None,
    #[default]
    Bounds,
    Domain,
}

// TODO ; avoid adding PartialEq, Eq, PartialOrd, Ord, Hash in library..?
#[derive(Serialize, Deserialize)]
#[serde(remote = "ModelConfig")]
struct ModelConfigDef<C: Coefficient> {
    #[serde(with = "ScmDef")]
    scm: Scm,
    cutoff: Option<C>,
    #[serde(with = "DecomposerDef")]
    decomposer: Decomposer,
    add_consistency: bool,
    #[serde(with = "ConsistencyDef")]
    propagate: Consistency,
}

// impl<C: Coefficient> From<(Experiment, Option<C>, Scm)> for ModelConfigDef<C> {
//     fn from((exp, cutoff, scm): (Experiment, Option<C>, Scm)) -> Self {
//         Self {
//             scm,
//             cutoff,
//             decomposer: Decomposer::try_from(exp.pb_encoding).unwrap(),
//             add_consistency: exp.add_consistency == AddConsistency::Aux,
//         }
//     }
// }

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
    pub principal: Option<Lit>,
    pub time: Option<f32>,
    pub dimacs: Option<PathBuf>,
    // pub obj: Option<Obj<Lit, C>>,
}

#[derive(Debug, Deserialize, Serialize, Clone, Default)]
pub struct StaticsRecord {
    pub vars: usize,
    pub cls: usize,
    pub lits: usize,
}

impl<Lit: Literal> From<&Cnf<Lit>> for StaticsRecord {
    fn from(cnf: &Cnf<Lit>) -> Self {
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
    pub solution: Option<Vec<Lit>>,
    pub assignment: Option<Vec<(usize, C)>>,
    pub time: f32,
    pub cost: Option<C>,
    pub check: Option<Result<(), String>>,
}

impl core::fmt::Display for SolveRecord {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "Got {} with {:?}.. solution in {}s of cost {:?} with check {:?}",
            self.status,
            self.solution
                .as_ref()
                .map(|s| s[0..std::cmp::min(s.len(), 10)].to_vec()),
            self.time,
            self.cost,
            self.check
        )
    }
}

impl StaticsRecord {
    pub fn new(vars: usize, cls: usize, lits: usize) -> Self {
        Self { vars, cls, lits }
    }
}

impl Experiment {
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
            add_consistency: self
                .system
                .add_consistencies()
                .contains(&self.add_consistency)
                .then_some(self.add_consistency)
                .unwrap_or_else(|| self.system.add_consistencies().first().unwrap().clone()),
            propagate: self
                .system
                .propagates()
                .contains(&self.propagate)
                .then_some(self.propagate)
                .unwrap_or_else(|| *self.system.propagates().first().unwrap()),
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
                .contains(&self.add_consistency)
                .then_some(())
                .ok_or(format!("{:?}", self.add_consistency)),
        ]
        .into_iter()
        .collect()
    }
}
