#[cfg(test)]
mod test {
	// #[cfg(feature = "trace")]
	// use traced_test::test;

	use crate::linear::Part;
	use crate::linear::{LinearEncoder, StaticLinEncoder};
	use crate::{PosCoeff, TotalizerEncoder};
	use rand::Rng; // 0.6.5

	use crate::{
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		helpers::tests::TestDB,
		AdderEncoder,
		Comparator,
		LinExp,
		LinearAggregator,
		LinearConstraint,
		PairwiseEncoder,
	};


	#[test]
	fn test_rand_pb() {
		let n = 5;
		let m = 5;
		let mut rng = rand::thread_rng();
		let terms = (1..=n)
			.map(|i| (i, rng.gen_range(1..=m)))
			.collect::<Vec<_>>();
		let mut db = TestDB::new(n);

		let mut encoder = LinearEncoder::new(
			StaticLinEncoder::new(
				TotalizerEncoder::default().add_cutoff(Some(10)),
				AdderEncoder::default(),
				PairwiseEncoder::default(),
			),
			LinearAggregator::default(),
		);
		let con = LinearConstraint::new(LinExp::from_terms(&terms), Comparator::LessEq, n * m / 2);
        use crate::Encoder;
		encoder.encode(&mut db, &con).unwrap();
		// db.with_check(|sol| {
		//     {
		//         let con = LinearConstraint::new(
		//             LinExp::new() + (1, 3) + (2, 3) + (3, 1) + (4, 1) + (5, 3),
		//             Comparator::GreaterEq,
		//             2,
		//         );
		//         con.check(sol)
		//     }
		//     .is_ok()
		// })
		// .check_complete()
	}

	pub(crate) fn construct_terms(terms: &[(i32, i32)]) -> Vec<Part<i32, PosCoeff<i32>>> {
		terms
			.iter()
			.map(|(lit, coef)| Part::Amo(vec![(lit.clone(), PosCoeff::from(coef.clone()))]))
			.collect()
	}

	/*
	macro_rules! bench_suite {
		($encoder:expr) => {
			// #[test]
			fn test_rand_pb() {
				let n = 100;
				let m = 100;
				let mut rng = rand::thread_rng();
				let terms = (1..=n)
					.map(|i| (i, rng.gen_range(0..m)))
					.collect::<Vec<_>>();
				dbg!(&terms);
				assert_sol!(
					$encoder,
					4,
					&Linear {
						terms: construct_terms(&terms),
						cmp: LimitComp::LessEq,
						k: 4.into()
					} => vec![vec![1]]
				);
			}


		};
	}

	bench_suite!(TotalizerEncoder::default().add_cutoff(Some(2)));
	*/
}
