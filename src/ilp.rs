use crate::{check_enc_timer, get_uniform_sampler};
use crate::{
    cli::{ConEncoding, Experiment, IntEncoding, PbEncoding, System},
    encode_bkp,
    formula::{EncodeErr, Formula, Lit, C},
    generate_mbkp, Cardinality, Encoder, PbcEncoder,
};
use bzip2::read::BzDecoder;

use flate2::bufread::GzDecoder;
use serde::{Deserialize, Serialize};

use std::{collections::HashSet, io::Read};
use std::{io::BufReader, process::Command};

use itertools::{Itertools, Position};
use std::fs::File;
use std::io::Error;
use std::io::Write;
use std::path::PathBuf;

use std::time::Instant;

use std::collections::HashMap;

use pindakaas::{
    ClauseDatabase, Cnf, Comparator, LinExp, LinVariant, LinearConstraint, LinearEncoder, Model,
    Result, Wcnf,
};
use std::rc::Rc;

use std::fmt;

#[derive(Debug, Clone)]
pub enum Obj {
    Minimize(Option<IlpExp>),
    Maximize(Option<IlpExp>),
    Satisfy,
}

impl<'de> Deserialize<'de> for Obj {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        match String::deserialize(deserializer).unwrap().as_str() {
            "Minimize" => Ok(Obj::Minimize(None)),
            "Maximize" => Ok(Obj::Maximize(None)),
            "Satisfy" => Ok(Obj::Satisfy),
            obj => Err(D::Error::custom(format!("Unexpected Obj {obj}"))),
        }
    }
}

impl Serialize for Obj {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Obj::Minimize(_) => serializer.serialize_str("Minimize"),
            Obj::Maximize(_) => serializer.serialize_str("Maximize"),
            Obj::Satisfy => serializer.serialize_str("Satisfy"),
        }
    }
}

impl Obj {
    pub fn obj(&self) -> Option<&IlpExp> {
        match self {
            Obj::Minimize(obj) | Obj::Maximize(obj) => Some(obj.as_ref().unwrap()),
            Obj::Satisfy => None,
        }
    }

    pub fn is_satisfy(&self) -> bool {
        matches!(self, Obj::Satisfy)
    }

    pub fn is_maximize(&self) -> bool {
        matches!(self, Obj::Maximize(_))
    }
}
#[derive(Debug, Clone)]
pub struct Ilp {
    pub int_vars: HashMap<usize, Rc<IntVar>>,
    pub ils: Vec<Il>,
    pub obj: Obj,
}

impl Ilp {
    pub fn from_hash_map(int_vars: HashMap<usize, Rc<IntVar>>, ils: Vec<Il>, obj: Obj) -> Self {
        Self { int_vars, ils, obj }
    }

    pub fn new(int_vars: Vec<Rc<IntVar>>, ils: Vec<Il>, obj: Obj) -> Self {
        Self {
            int_vars: HashMap::from_iter(int_vars.into_iter().map(|iv| (iv.get_id(), iv))),
            ils,
            obj,
        }
    }
    pub fn analyze(
        &self,
        _quick: bool,
    ) -> Result<(usize, C, Option<crate::cli::PbStaticsRecord>), EncodeErr> {
        todo!();
        /*
        let pbc = PbcEncoder {
            mode: Mode::Analyze,
            ..Default::default()
        };

        let lins = self
            .ils
            .iter()
            .filter(|il| il.lin.coefs.iter().any(|c| c.abs() > 1))
            .count();

        let max_k = self.ils.iter().map(|il| il.k.abs()).max().unwrap();

        if quick {
            return Ok((lins, max_k, None));
        }

        let agg = LinearAggregator::default();
        let mut encoder = LinearEncoder::new(pbc, agg);
        let mut formula = Formula::new(model, None, None);
        self.encode(
            &mut formula,
            &mut encoder,
            &Experiment::default(),
            None,
            None,
            false,
        )?;
        Ok((lins, max_k, Some(encoder.enc.pb_statics.clone())))
        */
    }

    pub fn from_mbkp(
        n_: usize,
        bound: usize,
        m_: usize,
        q_: usize,
        family: u32,
        s_: u32,
        seed: u64,
        skip_obj: bool,
    ) -> Model<Lit, C> {
        let (m_, weights, max_weight, profits, min_profit) =
            generate_mbkp(n_, bound, m_, q_, family, s_, seed);
        encode_bkp(m_, weights, max_weight, profits, min_profit, skip_obj)
    }

    pub fn from_file(path: PathBuf) -> Result<Self, String> {
        let mut vars: HashMap<String, (C, C)> = HashMap::new();
        let mut ils: Vec<(ParseLinExp, Comparator, C, Option<String>)> = vec![];

        type ParseLinExp = (Vec<String>, Vec<C>);

        let set_bounds = |var: &str, lb: &str, ub: &str, vars: &mut HashMap<String, (C, C)>| {
            //let id = var[1..].parse::<usize>().unwrap();
            let bnds = (lb.parse::<C>().unwrap(), ub.parse::<C>().unwrap());
            vars.entry(var.to_string())
                .and_modify(|var| *var = bnds)
                .or_insert(bnds);
        };

        #[derive(Debug, PartialEq)]
        enum ParseObj {
            Minimize(ParseLinExp),
            Maximize(ParseLinExp),
            Satisfy,
        }

        #[derive(PartialEq)]
        enum State {
            None,
            SubjectTo,
            Binary,
            Bounds,
            Minimize,
            Maximize,
            Satisfy,
        }

        let mut obj = ParseObj::Satisfy;

        let mut state = State::None;

        let ext = path.extension().unwrap().to_str().unwrap();
        let file = File::open(path.clone()).unwrap();
        let mut s = String::new();

        if ext == "gz" {
            GzDecoder::new(BufReader::new(file))
                .read_to_string(&mut s)
                .unwrap();
        } else if ext == "bz2" {
            BzDecoder::new(file).read_to_string(&mut s).unwrap();
        } else if ext == "lp" || ext == "opb" {
            BufReader::new(file).read_to_string(&mut s).unwrap();
        } else {
            panic!("Unknown ext {ext}");
        }

        let is_lp = ext != "opb" && ext != "bz2";

        // (var name as string, coefficient)
        let mut il: ParseLinExp = (vec![], vec![]);

        let mut lbl: Option<String> = None;
        let mut cmp: Option<Comparator> = None;
        let mut k: Option<C> = None;
        let mut is_positive: bool = true;

        for (i, line) in s.lines().enumerate() {
            if is_lp {
                match line
                    .to_lowercase()
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .as_slice()
                {
                    [] | ["*", "\\", ..] => continue,
                    line if matches!(line[0].chars().next(), Some('*' | '\\')) => continue,
                    ["end"] => break,
                    ["subject", "to"] | ["st" | "s.t."] => {
                        match state {
                            State::Minimize => {
                                obj = ParseObj::Minimize(il);
                            }
                            State::Maximize => {
                                obj = ParseObj::Maximize(il);
                            }
                            _ => {
                                obj = ParseObj::Satisfy;
                            }
                        }
                        cmp = None;
                        k = None;
                        il = (vec![], vec![]);
                        is_positive = true;
                        state = State::SubjectTo;
                        lbl = None;
                    }
                    ["binary" | "binaries" | "bin"] => {
                        state = State::Binary;
                    }
                    ["bounds"] => {
                        state = State::Bounds;
                    }
                    ["generals" | "general" | "gen" | "semi-continuous" | "semis" | "semi"] => {
                        return Err(String::from(
                            "Generals/semi-continuous sections not supported",
                        ));
                    }
                    ["minimize" | "minimum" | "min"] => state = State::Minimize,
                    ["maximize" | "maximum" | "max"] => state = State::Maximize,
                    [var, "=", val] if state == State::Bounds => {
                        set_bounds(var, val, val, &mut vars);
                    }
                    [lb, "<=", var, "<=", ub] if state == State::Bounds => {
                        set_bounds(var, lb, ub, &mut vars);
                    }
                    [var, ">=", lb] if state == State::Bounds => {
                        return Err(format!("Unsupported single bound setting for {var}>={lb}"));
                    }
                    xs if state == State::Binary => {
                        xs.iter().for_each(|x| {
                            set_bounds(x, "0", "1", &mut vars);
                        });
                    }
                    line if matches!(
                        state,
                        State::SubjectTo | State::Minimize | State::Maximize
                    ) =>
                    {
                        for token in line {
                            match *token {
                                "->" => {
                                    return Err(format!(
                                        "Indicator variables (in cons {lbl:?}) not supported",
                                    ));
                                }
                                ">=" => {
                                    cmp = Some(Comparator::GreaterEq);
                                }
                                "<=" => {
                                    cmp = Some(Comparator::LessEq);
                                }
                                "=" => {
                                    cmp = Some(Comparator::Equal);
                                }
                                "+" => {
                                    is_positive = true;
                                }
                                "-" => {
                                    is_positive = false;
                                }
                                token => {
                                    if let Some(next_lbl) = token.strip_suffix(':') {
                                        lbl = Some(next_lbl.to_string());
                                    } else if token.chars().next().unwrap().is_alphabetic()
                                        || token.starts_with('_')
                                    {
                                        let var = token.to_string();
                                        il.0.push(var);
                                        // if we didn't see a coefficient, it should be +/- 1
                                        if il.1.len() == il.0.len() - 1 {
                                            il.1.push(if is_positive { 1 } else { -1 });
                                            is_positive = true;
                                        }
                                    } else {
                                        let coef = token.parse::<C>().map_err(|_| {
                                            format!("Failed parsing to integer on {token}")
                                        })?;
                                        if cmp.is_some() {
                                            k = Some(coef);
                                        } else {
                                            il.1.push(if is_positive { coef } else { -coef });
                                            is_positive = true;
                                        }
                                    }
                                }
                            }
                        }

                        // push last constraint/obj if exists
                        if let (Some(curr_cmp), Some(curr_k)) = (cmp, k) {
                            ils.push((il, curr_cmp, curr_k, Some(lbl.unwrap().to_string())));
                            lbl = None;
                            cmp = None;
                            k = None;
                            il = (vec![], vec![]);
                            is_positive = true;
                        }

                        assert!(
                        il.0.len() == il.1.len(),
                        "Got unequal number of vars/coefs ({}/{}) with {il:?} for line {line:?}",
                        il.0.len(),
                        il.1.len()
                    );
                    }
                    err => {
                        return Err(err.join(" "));
                    }
                }
            } else {
                if line.starts_with('*') {
                    continue;
                }
                match line
                    .to_lowercase()
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .as_slice()
                {
                    [] => continue,
                    line => {
                        for token in line {
                            match *token {
                                ">=" => {
                                    cmp = Some(Comparator::GreaterEq);
                                }
                                "<=" => {
                                    cmp = Some(Comparator::LessEq);
                                }
                                "=" => {
                                    cmp = Some(Comparator::Equal);
                                }
                                ";" => {}
                                token => {
                                    if token.chars().next().unwrap().is_alphabetic()
                                        || token.starts_with('x')
                                    {
                                        let var = token.to_string();
                                        set_bounds(&var, "0", "1", &mut vars);
                                        il.0.push(var);

                                        // if we didn't see a coefficient, it should be +/- 1
                                        // if il.1.len() == il.0.len() - 1 {
                                        //     // il.1.push(if is_positive { 1 } else { -1 });
                                        //     // il.1.push(if is_positive { 1 } else { -1 });
                                        //     // is_positive = true;
                                        // }
                                    } else {
                                        // let is_positive = token.starts_with('+');
                                        let coef = token.parse::<C>().map_err(|_| {
                                            format!("Failed parsing to integer on {token}")
                                        })?;
                                        if cmp.is_some() {
                                            k = Some(coef);
                                        } else {
                                            // il.1.push(if is_positive { coef } else { -coef });
                                            il.1.push(coef);
                                        }
                                    }
                                }
                            }
                        }

                        ils.push((
                            il,
                            cmp.unwrap(),
                            k.unwrap(),
                            Some(lbl.unwrap_or_else(|| i.to_string()).to_string()),
                        ));
                        il = (vec![], vec![]);
                        lbl = None;
                        cmp = None;
                        k = None;
                    }
                }
            }
        }

        let vars = vars
            .into_iter()
            .sorted()
            .enumerate()
            .map(|(id, (lp_id, (lb, ub)))| {
                (lp_id, Rc::new(IntVar::new(id + 1, (lb..=ub).collect())))
            })
            .collect::<HashMap<_, _>>();

        let to_ilp_exp = |(int_vars, coefs): ParseLinExp| IlpExp {
            int_vars: int_vars
                .into_iter()
                .flat_map(|lp_id| {
                    vars.get(&lp_id)
                        .ok_or(format!("Unbounded variable {lp_id}"))
                        .map(Rc::clone)
                })
                .collect(),
            coefs,
        };

        let ils = ils
            .into_iter()
            .map(|(lin, cmp, k, lbl)| Il {
                lin: to_ilp_exp(lin),
                cmp,
                k,
                lbl,
            })
            .collect();
        let obj = match obj {
            ParseObj::Maximize(lin) => Obj::Maximize(Some(to_ilp_exp(lin))),
            ParseObj::Minimize(lin) => Obj::Minimize(Some(to_ilp_exp(lin))),
            ParseObj::Satisfy => Obj::Satisfy,
        };

        let obj = match obj {
            Obj::Minimize(lin) | Obj::Maximize(lin)
                if {
                    let lin = lin.as_ref().unwrap();
                    lin.coefs.iter().all(|c| c == &0)
                        || lin.int_vars.iter().all(|x| x.dom().count() == 1)
                } =>
            {
                Obj::Satisfy
            }
            _ => obj,
        };

        Ok(Ilp::from_hash_map(
            vars.into_values()
                .map(|int_var| (int_var.get_id(), int_var))
                .collect(),
            ils,
            obj,
        ))
    }

    pub fn to_file(&self, path: PathBuf) -> Result<(), Error> {
        let mut output = File::create(path)?;
        writeln!(
            output,
            "\\ #variable= {} #constraint= {}",
            self.int_vars.len(),
            self.ils.len()
        )?;

        let lin_to_string = |lin: &IlpExp| -> String {
            lin.int_vars
                .iter()
                .zip(lin.coefs.iter())
                .map(|(int_var, coef)| {
                    format!(
                        "{} {} x{}",
                        if coef.is_positive() { "+" } else { "-" },
                        coef.abs(),
                        int_var.get_id()
                    )
                })
                .join(" ")
        };

        match &self.obj {
            Obj::Satisfy => {}
            Obj::Maximize(Some(lin)) => writeln!(output, "Max {}", lin_to_string(lin))?,
            Obj::Minimize(Some(lin)) => writeln!(output, "Min {}", lin_to_string(lin))?,
            _ => unreachable!(),
        }

        writeln!(output, "Subject To",)?;
        for (i, il) in self.ils.iter().enumerate() {
            writeln!(
                output,
                "  c{}: {}",
                i,
                std::iter::once(lin_to_string(&il.lin))
                    .chain(std::iter::once(match il.cmp {
                        Comparator::LessEq => String::from("<="),
                        Comparator::GreaterEq => String::from(">="),
                        Comparator::Equal => String::from("="),
                    }))
                    .chain(std::iter::once(format!("{}", il.k)))
                    .join(" ")
            )?;
        }

        writeln!(output, "Bounds")?;
        for (_, int_var) in self.int_vars.iter().sorted_by_key(|int_var| int_var.0) {
            writeln!(
                output,
                "  {} <= x{} <= {}",
                int_var.lb(),
                int_var.get_id(),
                int_var.ub()
            )?;
        }
        writeln!(output, "End")?;
        Ok(())
    }

    pub fn essence(&self, eprime: String) -> Result<(), Error> {
        let mut output = File::create(eprime)?;

        assert!(
            self.int_vars
                .values()
                .all(|int_var| int_var.dom().collect::<HashSet<_>>()
                    == self.int_vars[&1].dom().collect()),
            "Non-binary variables not supported for essence"
        );

        writeln!(output, "language ESSENCE' 1.0")?;
        writeln!(
            output,
            "letting DOMS be domain int({})",
            self.int_vars[&1].dom().join(",")
        )?;
        writeln!(
            output,
            "find xs : matrix indexed by [int(1..{})] of DOMS",
            self.int_vars.len()
        )?;
        let write_terms = |lin: &IlpExp| {
            let it = lin
                .int_vars
                .iter()
                .zip(lin.coefs.iter())
                .map(|(x, c)| format!("{c}*xs[{}]", x.get_id()));

            Itertools::intersperse(it, " + ".to_string()).collect::<String>()
        };
        match &self.obj {
            Obj::Minimize(obj) | Obj::Maximize(obj) => {
                writeln!(
                    output,
                    "{} {}",
                    if self.obj.is_maximize() {
                        "maximising"
                    } else {
                        "minimising"
                    },
                    write_terms(obj.as_ref().unwrap())
                )
            }
            Obj::Satisfy => Ok(()),
        }?;

        writeln!(output, "such that")?;
        for il in self.ils.iter().with_position() {
            let (il, suffix) = match il {
                Position::Last(il) | Position::Only(il) => (il, ""),
                Position::First(il) | Position::Middle(il) => (il, ","),
            };
            let xs = write_terms(&il.lin);

            let cmp = match il.cmp {
                Comparator::LessEq => "<=",
                Comparator::Equal => "=",
                Comparator::GreaterEq => ">=",
            };
            let k = il.k;

            writeln!(output, "sum ([ {xs} ]) {cmp} {k}{suffix}",)?;
        }
        Ok(())
    }

    pub fn encode(
        &self,
        formula: &mut Formula,
        encoder: &mut LinearEncoder<PbcEncoder>,
        experiment: &Experiment,
        enc_timeout: Option<f32>,
        aux_out: Option<PathBuf>,
        opb_only: bool,
    ) -> Result<(HashMap<usize, Vec<Lit>>, Option<PathBuf>), EncodeErr> {
        let enc_timer = Instant::now();

        let Experiment {
            int_encoding,
            con_encoding,
            // cutoff, // TODO
            ..
        } = experiment;

        eprintln!("Encoding variables..");
        let enc = self
            .int_vars
            .iter()
            .sorted_by(|(a, _), (b, _)| a.cmp(b))
            .map(|(_, int_var)| {
                // let int_encoding = int_var.int_encoding(cutoff);

                (
                    int_var.get_id(),
                    (0..int_var.size(int_encoding))
                        .map(|_| formula.new_var())
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<HashMap<_, _>>();

        for int_var in self.int_vars.values() {
            let xs = &enc[&int_var.get_id()];

            // let int_encoding = int_var.int_encoding(cutoff);

            match int_encoding {
                // TODO need CardinalityConstraint?
                IntEncoding::Dir => {
                    formula
                        .encode_linear(
                            encoder,
                            LinearConstraint::<Lit, C>::new(
                                LinExp::from_terms(&xs.iter().map(|x| (*x, 1)).collect::<Vec<_>>()),
                                Comparator::Equal,
                                1,
                            ),
                            opb_only,
                        )
                        .unwrap();
                }
                IntEncoding::Ord => {
                    xs.iter().tuple_windows().for_each(|(a, b)| {
                        formula
                            .encode_linear(
                                encoder,
                                LinearConstraint::<Lit, C>::new(
                                    LinExp::from_terms(&[(*a, -1), (*b, 1)]),
                                    Comparator::LessEq,
                                    0,
                                ),
                                opb_only,
                            )
                            .unwrap()
                    });
                }
                IntEncoding::Bin => {
                    // TODO can be omitted if we this directly (and preferably only once) in a future totalizer/pb encoder
                    // TODO make this lex constraint (now default to experiment's encoding)
                    let lin_exp = LinExp::from_slices(&int_var.coefs(1, int_encoding), xs);
                    formula
                        .encode_linear(
                            encoder,
                            LinearConstraint::<Lit, C>::new(
                                lin_exp.clone(),
                                Comparator::GreaterEq,
                                int_var.lb(),
                            ),
                            opb_only,
                        )
                        .unwrap();
                    formula
                        .encode_linear(
                            encoder,
                            LinearConstraint::<Lit, C>::new(
                                lin_exp,
                                Comparator::LessEq,
                                int_var.ub(),
                            ),
                            opb_only,
                        )
                        .unwrap();
                }
            }
        }

        let collect_amos = false;
        let (ils, amos, cards) = if collect_amos {
            eprintln!("Finding AMOs/ICs..");

            let mut amos = Vec::new();
            let mut cards = Vec::new();
            let mut ils = Vec::new();
            for il in &self.ils {
                let Il {
                    k,
                    cmp,
                    lin,
                    lbl: _,
                } = il;

                let mut cnf = Cnf::<Lit>::new(formula.wcnf.variables() as Lit);

                let lin_exp =
                    lin.clone()
                        .into_lin_exp(&enc, int_encoding, con_encoding, &vec![], &[]);
                let constraint = LinearConstraint::<Lit, C>::new(lin_exp, *cmp, *k);
                match encoder.agg.aggregate(&mut cnf, &constraint).unwrap() {
                    LinVariant::Trivial => {
                        formula.merge_in(cnf).unwrap();
                    }
                    LinVariant::CardinalityOne(amo) => {
                        formula.merge_in(cnf).unwrap();
                        encoder
                            .enc
                            .encode(formula, &LinVariant::CardinalityOne(amo.clone()))
                            .unwrap();
                        amos.push(HashSet::from_iter(amo.lits.iter().cloned()));
                    }
                    LinVariant::Cardinality(card) => {
                        formula.merge_in(cnf).unwrap();
                        encoder
                            .enc
                            .encode(formula, &LinVariant::Cardinality(card.clone()))
                            .unwrap();
                        cards.push(card);
                    }
                    _ => ils.push(il),
                };
            }
            (ils, amos, cards)
        } else {
            (self.ils.iter().collect(), vec![], vec![])
        };

        assert!(amos.iter().map(|amo| amo.len()).sum::<usize>() == amos.iter().flatten().count());
        eprintln!("Encoding constraints..");
        let n_terms = ils.iter().map(|il| il.lin.int_vars.len()).sum::<usize>();
        let mut i_terms = 0;
        for (i, il) in ils.iter().enumerate() {
            i_terms += il.lin.int_vars.len();

            eprintln!(
                "{}/{} ({}/{} = {:.2}%)",
                i + 1,
                ils.len(),
                i_terms,
                n_terms,
                (i_terms as f32 / n_terms as f32) * 100.0
            );

            check_enc_timer(enc_timeout, enc_timer)?;

            let Il {
                k,
                cmp,
                lin,
                lbl: _,
            } = il;
            let lin_exp = lin
                .clone()
                .into_lin_exp(&enc, int_encoding, con_encoding, &amos, &cards);
            let constraint = LinearConstraint::<Lit, C>::new(lin_exp, *cmp, *k);

            formula
                .encode_linear(encoder, constraint, opb_only)
                .map_err(|_| EncodeErr::Unsatisfiable)?;
        }

        // if !skip_obj {
        //     if let Some(obj) = self.obj.clone() {
        //         println!("Encoding objective..");
        //         let obj = obj.into_lin_exp(&enc, int_encoding, con_encoding, &vec![], &[]);
        //         for (lit, coef) in obj.terms() {
        //             formula.add_weighted_clause(&[-lit], *coef).unwrap();
        //         }
        //     }
        // }
        //

        let dimacs = if experiment.system == System::PbLib {
            let aux_out = aux_out.unwrap();
            let mut opb = aux_out.clone();
            opb.set_extension("opb");
            formula.to_opb(opb.clone(), true).unwrap();
            check_enc_timer(enc_timeout, enc_timer)?;

            let mut dimacs = aux_out;
            dimacs.set_extension("dimacs");
            let dimacs_file = File::create(&dimacs).unwrap();

            Command::new("./bin/pblib/build/pbencoder")
                .arg(opb)
                .arg("amo_bdd") // should be equiv to ladder
                .arg(match experiment.pb_encoding {
                    PbEncoding::Swc => "pb_swc",
                    PbEncoding::Bdd => "pb_bdd",
                    PbEncoding::Adder => "pb_adder",
                    PbEncoding::Gpw => "watchdog",
                    PbEncoding::SortingNetwork => "pb_sorter",
                    PbEncoding::BinaryMerger => "bin_merge",
                    _ => unreachable!(),
                })
                .stdout(dimacs_file)
                .spawn()
                .expect("PBLIB spawn err")
                .wait()
                .expect("PBLIB output err");
            check_enc_timer(enc_timeout, enc_timer)?;
            formula.wcnf = Wcnf::from(Cnf::from_file(dimacs.as_path()).unwrap());
            Some(dimacs)
        } else if let Some(aux_out) = aux_out {
            let mut sat_out = aux_out;
            sat_out.set_extension("dimacs");
            // let dimacs = formula.write(Some(sat_out), &self.obj);
            let dimacs = formula.write(Some(sat_out), &pindakaas::Obj::Satisfy);
            check_enc_timer(enc_timeout, enc_timer)?;
            Some(dimacs)
        } else {
            None
        };

        Ok((enc, dimacs))
    }

    pub fn principal(&self, int_encoding: &IntEncoding) -> Lit {
        self.int_vars
            .values()
            .map(|x| x.size(int_encoding) as Lit)
            .sum::<Lit>()
    }

    pub fn assign_ints(
        &self,
        lit_assignment: &HashMap<Lit, bool>,
        enc: &HashMap<usize, Vec<Lit>>,
        int_encoding: &IntEncoding,
    ) -> HashMap<usize, C> {
        self.int_vars
            .iter()
            .map(|(id, int_var)| {
                let xs = &enc[id];
                let coefs = int_var.coefs(1, int_encoding).into_iter();
                (
                    int_var.get_id(),
                    int_var.lb()
                        + xs.iter()
                            .zip(coefs)
                            .map(|(x, q)| (lit_assignment[x] as C) * q)
                            .sum::<C>(),
                )
            })
            .collect()
    }

    pub fn get_int_var(&self, id: usize) -> Rc<IntVar> {
        Rc::clone(&self.int_vars[&id])
    }

    pub fn from_soh(n: usize, d: usize) -> Self {
        // let mut sample = get_uniform_sampler(1..(q as C + 1), seed);

        let xs = (1..=n)
            .map(|i| Rc::new(IntVar::new(i, HashSet::from_iter(0..=(d as C)))))
            .collect::<Vec<_>>();

        let ys = (1..=n)
            .map(|i| Rc::new(IntVar::new(n + i, HashSet::from_iter(0..=(d as C)))))
            .collect::<Vec<_>>();

        let cons = xs
            .iter()
            .zip(ys.iter())
            .enumerate()
            .map(|(i, (x, y))| {
                Il::new(
                    vec![x.clone(), y.clone()],
                    vec![1, -1],
                    Comparator::GreaterEq,
                    0,
                    format!("A{i}").into(),
                )
            })
            .chain(std::iter::once(Il::new(
                [xs.clone(), ys.clone()].into_iter().flatten().collect(),
                xs.iter().map(|_| 1).chain(ys.iter().map(|_| -1)).collect(),
                Comparator::LessEq,
                -1,
                Some(String::from("B")),
            )))
            .collect::<Vec<_>>();

        Ilp::new([xs, ys].into_iter().flatten().collect(), cons, Obj::Satisfy)
    }
    pub fn from_rand_eqs(n: usize, m: usize, b: usize, q: usize, seed: u64) -> Self {
        let mut sample = get_uniform_sampler(1..(q as C + 1), seed);
        let css = (1..=n)
            .map(|_| (1..=m).map(|_| sample()).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let int_vars = (1..=m)
            .map(|j| Rc::new(IntVar::new(j, HashSet::from_iter(0..=(b as C)))))
            .collect::<Vec<_>>();

        let mut sample = get_uniform_sampler(0..(b as C + 1), seed);
        let solution = int_vars.iter().map(|_| sample()).collect::<Vec<_>>();
        let ks = (1..=n)
            .map(|i| {
                (1..=m)
                    .map(|j| css[i - 1][j - 1] * solution[j - 1])
                    .sum::<C>()
            })
            .collect::<Vec<_>>();
        let cons = css
            .into_iter()
            .zip(ks)
            .enumerate()
            .map(|(i, (cs, k))| {
                Il::new(
                    int_vars.iter().map(Rc::clone).collect(),
                    cs,
                    Comparator::Equal,
                    k,
                    format!("c{i}").into(),
                )
            })
            .collect::<Vec<_>>();

        Ilp::new(int_vars, cons, Obj::Satisfy)
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct IntVar {
    id: usize,
    dom: HashSet<C>,
}

impl IntVar {
    pub fn new(id: usize, dom: HashSet<C>) -> Self {
        Self { id, dom }
    }

    pub fn get_id(&self) -> usize {
        self.id
    }

    pub fn dom(&self) -> impl Iterator<Item = &C> {
        self.dom.iter().sorted()
    }

    pub fn set_ub(&mut self, ub: C) {
        self.dom = (self.lb()..=ub).collect();
    }

    pub fn lb(&self) -> C {
        *self.dom().min().unwrap()
    }

    pub fn ub(&self) -> C {
        *self.dom().max().unwrap()
    }

    pub fn size(&self, int_encoding: &IntEncoding) -> usize {
        match int_encoding {
            IntEncoding::Dir => self.dom().count(), // includes 0..ub -> x=0, x=1, x=2 ... =  ub+1 variables
            IntEncoding::Ord => self.dom().count() - 1, // includes 0..ub = x>=0, x>=1, .. = ub variables since x>=0 = 1
            IntEncoding::Bin => 1 + ((self.ub() as f32).log2()).floor() as usize,
        }
    }

    pub fn coefs(&self, q: C, int_encoding: &IntEncoding) -> Vec<C> {
        (0..self.size(int_encoding))
            .map(|j| match int_encoding {
                IntEncoding::Dir => q * (j as C),
                IntEncoding::Ord => q,
                IntEncoding::Bin => q * (2usize.pow(j as u32)) as C,
            })
            .collect()
    }

    fn int_encoding(&self, cutoff: &Option<C>) -> IntEncoding {
        match cutoff {
            None => IntEncoding::Ord,
            Some(0) => IntEncoding::Bin,
            Some(cutoff) => {
                if self.dom.len() < *cutoff as usize {
                    IntEncoding::Ord
                } else {
                    IntEncoding::Bin
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct IlpExp {
    int_vars: Vec<Rc<IntVar>>,
    coefs: Vec<C>,
}

impl IlpExp {
    pub fn new(int_vars: Vec<Rc<IntVar>>, coefs: Vec<C>) -> Self {
        Self { int_vars, coefs }
    }

    pub fn assign(&self, assignment: &HashMap<usize, C>) -> C {
        self.int_vars
            .iter()
            .zip(self.coefs.iter())
            .fold(0, |acc, (int_var, coef)| {
                acc + assignment[&int_var.get_id()] * coef
            })
    }

    pub fn into_lin_exp(
        self,
        enc: &HashMap<usize, Vec<Lit>>,
        int_encoding: &IntEncoding,
        con_encoding: &ConEncoding,
        amos: &Vec<HashSet<Lit>>,
        _cards: &[Cardinality<Lit, C>],
    ) -> LinExp<Lit, C> {
        let mut lin_exp = LinExp::new();

        let mut k = 0;
        let terms = self
            .int_vars
            .iter()
            .zip(self.coefs.iter())
            .filter_map(|(int_var, coef)| {
                if int_var.dom.len() == 1 {
                    k += coef * int_var.dom.iter().next().unwrap();
                    None
                } else {
                    Some((
                        int_var,
                        enc[&int_var.get_id()].clone(),
                        int_var.coefs(*coef, int_encoding),
                    ))
                }
            })
            .collect::<Vec<_>>();

        lin_exp = lin_exp.add_constant(k);

        let amos = if amos.is_empty() {
            HashMap::from_iter([(None, terms)])
        } else {
            terms
                .into_iter()
                .map(|(int_var, lits, coef)| {
                    assert!(lits.len() == 1);
                    (
                        amos.iter().position(|amo| amo.contains(&lits[0])),
                        (int_var, lits, coef),
                    )
                })
                .into_group_map()
        };

        for (amo, terms) in amos {
            let terms_n = terms.len();
            let int_var_terms = terms
                .into_iter()
                .map(|(int_var, lits, coefs)| {
                    (
                        int_var,
                        lits.into_iter().zip(coefs.into_iter()).collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>();

            if matches!(con_encoding, ConEncoding::Include) && amo.is_some() && terms_n > 1 {
                let choice = int_var_terms
                    .into_iter()
                    .flat_map(|x| x.1)
                    .collect::<Vec<_>>();
                lin_exp = lin_exp.add_choice(&choice);
            } else {
                for (int_var, terms) in int_var_terms {
                    match con_encoding {
                        ConEncoding::Ignore => {
                            lin_exp += LinExp::from_terms(&terms);
                        }
                        ConEncoding::Include => {
                            // TODO [?] make these not return self (so we don't forget lin_exp = ..)?
                            match int_encoding {
                                IntEncoding::Dir => {
                                    lin_exp = lin_exp.add_choice(&terms);
                                }
                                IntEncoding::Ord => {
                                    lin_exp = lin_exp.add_chain(&terms);
                                }
                                IntEncoding::Bin => {
                                    lin_exp = lin_exp.add_bounded_log_encoding(
                                        &terms,
                                        int_var.lb(),
                                        int_var.ub(),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        lin_exp
    }
}

#[derive(Debug, Clone)]
pub struct Il {
    lin: IlpExp,
    cmp: Comparator,
    k: C,
    lbl: Option<String>,
}

impl Il {
    pub fn new(
        int_vars: Vec<Rc<IntVar>>,
        coefs: Vec<C>,
        cmp: Comparator,
        k: C,
        lbl: Option<String>,
    ) -> Self {
        Self {
            lin: IlpExp { int_vars, coefs },
            cmp,
            k,
            lbl,
        }
    }
}

fn write_constraint(
    ids: &Vec<C>,
    coefs: &[C],
    ubs: Option<&Vec<C>>,
    cmp: &Comparator,
    k: &C,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    // for (id, coef, ub) in ids.iter().zip(coefs.iter()).zip(ubs.iter()) {
    for i in 0..ids.len() {
        let id = ids[i];
        let coef = coefs[i];
        write!(
            f,
            " {}{}{}x{}",
            if coef.is_negative() { "-" } else { "+" },
            if coef.abs() != 1 {
                format!("{}*", coef.abs())
            } else {
                String::from("")
            },
            if id.is_negative() { "-" } else { "" },
            id.abs()
        )?;
        if let Some(ubs) = ubs {
            if ubs[i] > 1 {
                write!(f, " in 0..{}", ubs[i])?;
            }
        }
    }
    write!(
        f,
        " {} {}",
        match cmp {
            Comparator::LessEq => "<=",
            Comparator::GreaterEq => ">=",
            Comparator::Equal => "=",
        },
        k
    )?;
    Ok(())
}

impl fmt::Display for Ilp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Ilp:")?;
        for il in &self.ils {
            write!(f, "\t{}", il)?;
        }
        Ok(())
    }
}

impl fmt::Display for Il {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, " Il [lbl={:?}]:", self.lbl)?;
        write_constraint(
            &self
                .lin
                .int_vars
                .iter()
                .map(|int_var| int_var.id as C)
                .collect(),
            &self.lin.coefs,
            Some(
                &self
                    .lin
                    .int_vars
                    .iter()
                    .map(|int_var| int_var.ub() as C)
                    .collect(),
            ),
            &self.cmp,
            &self.k,
            f,
        )?;
        Ok(())
    }
}

//#[cfg(test)]
//mod tests {
//    use super::*;
//    use std::path::PathBuf;
//    use std::str::FromStr;
//    #[test]
//    fn read_test() {
//        let path = PathBuf::from_str("./instances/miplib/10teams.lp.gz").unwrap();
//        let ilp = Ilp::from_file(path.clone()).unwrap();
//        let out = PathBuf::from_str("./experiments/dev/test.lp").unwrap();
//        ilp.to_file(out.clone()).unwrap();
//        let _ilp2 = Ilp::from_file(out);
//        //assert!(ilp == ilp2);
//    }

//    #[test]
//    fn read_opb_test() {
//        // let path = PathBuf::from_str("./instances/integration/pb.opb").unwrap();
//        let path = PathBuf::from_str("instances/pb/PB15eval/normalized-PB15eval/DEC-SMALLINT-LIN/ProofComplexity-Extracted-Cardinality-Constraints/ProofComplexity/normalized-tseitin-regular-n66-d3-i3-r1.cnf.gz-plain.pb.metafix.opb.bz2").unwrap();
//        let ilp = Ilp::from_file(path.clone()).unwrap();
//        let out = PathBuf::from_str("./experiments/integration/opb.lp").unwrap();
//        ilp.to_file(out.clone()).unwrap();
//        let _ilp2 = Ilp::from_file(out);
//        //assert!(ilp == ilp2);
//    }
// }
