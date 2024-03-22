use std::path::PathBuf;
use std::{collections::HashMap, fs::File, path::Path};

use itertools::iproduct;
use itertools::Itertools;
use pindakaas::Decomposer;
use pindakaas::{Cnf, Format, Model, ModelConfig, Scm};
// use tabled::builder::Builder;

use crate::analyze::Mkplot;
use crate::{
    analyze::avg,
    cli::Run,
    formula::{Lit, C},
};

pub fn scm(run: Run) -> Result<(), String> {
    if let Run::Scm {
        bl,
        bu,
        cl,
        cu,
        fmt,
    } = run
    {
        let bits = bl..=bu;
        let cs = cl..=cu;

        let scms = [Scm::Add, Scm::Rca, Scm::Pow, Scm::Dnf];
        // let scms = [Scm::Add];

        let data = iproduct!(bits.clone(), cs.clone(), scms.clone())
            .flat_map(|(b, c, scm)| {
                if scm == Scm::Dnf && b > 12 {
                    return None;
                }
                let ub = 2u32.pow(b) - 1;
                let lp = format!(
                    "
Subject To
c0: + {c} x1 = 0
Bounds
0 <= x1 <= {ub}
End
"
                )
                .to_string();

                let descr = if scm == Scm::Add {
                    Some(
                        std::fs::read_to_string(Path::new(&format!(
                            "./bin/pindakaas/crates/pindakaas/res/scm/{b}_{c}.txt"
                        )))
                        .unwrap_or_default(),
                    )
                } else {
                    None
                };

                let mut db = Cnf::new(0);
                let mut model = Model::<Lit, C>::from_string(lp.clone(), Format::Lp)
                    .unwrap()
                    .with_config(ModelConfig {
                        scm: scm.clone(),
                        cutoff: Some(0),
                        decomposer: Decomposer::Rca,
                        ..ModelConfig::default()
                    });

                // let extra = (0u32.leading_zeros() - (c * ub).leading_zeros()) as usize;

                // TODO this statistics includes the unary constraint "== 0"; encode just the Term!
                model.encode(&mut db).unwrap();
                Some((
                    (b, c, scm),
                    (
                        db.variables(),
                        // db.clauses() - extra,
                        // db.literals() - extra,
                        db.clauses(),
                        db.literals(),
                        descr,
                        // lp,
                        String::from(""),
                        // db.to_string(),
                    ),
                ))
            })
            .collect::<HashMap<_, _>>();

        // let mut builder = Builder::default();

        let mut writer = csv::Writer::from_writer(File::create("scm.csv").unwrap());

        const EXTENDED: bool = true;

        let cols = iproduct!(bits, scms);

        // HEADERS
        writer
            .write_record(
                ["".to_string()]
                    .into_iter()
                    .chain(cols.clone().flat_map(|(b, scm)| {
                        [
                            [
                                format!("b={b},scm={scm:?}").to_string(),
                                "".to_string(),
                                "".to_string(),
                            ]
                            .to_vec(),
                            if EXTENDED {
                                ["".to_string(), "".to_string()].to_vec()
                            } else {
                                [].to_vec()
                            }
                            .to_vec(),
                        ]
                        .concat()
                    }))
                    .collect::<Vec<_>>(),
            )
            .unwrap();

        writer
            .write_record(
                ["c".to_string()]
                    .into_iter()
                    .chain(cols.clone().flat_map(|(_, _)| {
                        [
                            ["vars", "cls", "lits"].to_vec(),
                            if EXTENDED {
                                ["LP", "CNF"].to_vec()
                            } else {
                                [].to_vec()
                            },
                        ]
                        .concat()
                        .into_iter()
                        .map(String::from)
                        .collect::<Vec<_>>()
                    }))
                    .collect::<Vec<_>>(),
            )
            .unwrap();

        struct AvgRow {
            variables: f32,
            clauses: f32,
            literals: f32,
        }

        let avgs = data
            .clone()
            .into_iter()
            .into_group_map_by(|((_, _, scm), _)| scm.clone())
            .into_iter()
            .map(|(scm, data)| {
                (
                    scm,
                    data.into_iter()
                        .into_group_map_by(|((b, _, _), _)| *b)
                        .into_iter()
                        .map(|(b, data)| {
                            (b, {
                                let (vars, cls, lits): (Vec<_>, Vec<_>, Vec<_>) = data
                                    .iter()
                                    .map(|(_, (vars, cls, lits, _, _))| {
                                        (Some(*vars as f32), Some(*cls as f32), Some(*lits as f32))
                                    })
                                    .multiunzip();
                                (
                                    avg(&vars, None).unwrap(),
                                    avg(&cls, None).unwrap(),
                                    avg(&lits, None).unwrap(),
                                )
                            })
                        })
                        .collect_vec(),
                )
            })
            .sorted_by_key(|(key, _)| key.clone())
            .collect::<Vec<_>>();

        // let tex = format!("")
        // for avg in avgs {
        // }

        let jsons = PathBuf::from("experiments/scm/jsons");
        let plots = PathBuf::from("experiments/scm/plots");

        [
            Mkplot::scm_static(&avgs, 0),
            Mkplot::scm_static(&avgs, 1),
            Mkplot::scm_static(&avgs, 2),
        ]
        .into_iter()
        .for_each(|p| {
            p.plot(&jsons, &plots, &fmt);
        });

        //         println!("AVG : {}", avgs.iter().map(|x| format!("{x:?}")).join(","));
        //         // AVGs
        //         writer
        //             .write_record(
        //                 [String::from("avgs:")]
        //                     .into_iter()
        //                     .chain(avgs.iter().map(|x| format!("{x:?}")))
        //                     .collect::<Vec<_>>(),
        //             )
        //             .unwrap();

        // builder.set_columns(header.clone());

        for c in cs.clone() {
            let record = [format!("c={c}")]
                .into_iter()
                .chain(cols.clone().flat_map(|(b, scm)| {
                    (data)
                        .get(&(b, c, scm))
                        .map(|s| {
                            [
                                [s.0.to_string(), s.1.to_string(), s.2.to_string()].to_vec(),
                                if EXTENDED {
                                    [format!("{:?}", s.3), s.4.clone()].to_vec()
                                } else {
                                    [].to_vec()
                                },
                            ]
                            .concat()
                        })
                        .unwrap_or_else(|| {
                            ["?"; if EXTENDED { 5 } else { 3 }]
                                .into_iter()
                                .map(String::from)
                                .collect::<Vec<_>>()
                        })
                        .clone()
                }))
                .collect::<Vec<_>>();
            writer.write_record(record.clone()).unwrap();
            // builder.add_record(record);
        }

        // for line in  {
        //     if line.is_empty() {
        //         continue;
        //     }

        //     let words: Vec<_> = line.trim().split_terminator(' ').collect();
        //     builder.push_record(words);
        // }

        // let columns = (0..builder.count_columns()).map(|i| i.to_string());
        // builder.set_header(columns);

        // let table = builder.build();
        // table.with(Style::ascii_rounded());

        // println!("{}", table);
        Ok(())
    } else {
        unreachable!()
    }
}
