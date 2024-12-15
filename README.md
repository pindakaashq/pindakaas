# PBC/Pindakaas from CPAIOR'25 submission

Dependencies:

- Rust `>=1.82` (for main implementation)
- JRE `>=23` (optional, for control encoders Savile Row and Fun-sCOP)
- MiniZinc `>=2.8.5` (optional, for control encoder Picat-SAT)
- Tectonic  `>=0.15.0` (optional, to compile the latex table from the paper)

With these dependencies installed, we can build the tooling and analyze the results presented in the paper

```
# Build software; control encoder dependencies should be already included in `bin`, otherwise they are downloaded if their directory is removed.
./build.sh
# Check, analyze, and compile latex table for the results presented in the paper
cargo run -r analyze experiments/mbkp experiments/mbkp-control experiments/mbssp experiments/mbssp-control --table --check
```

To reproduce the experiments with Slurm, change the `nodelist` parameter in each `experiments/*/slurm.json` to what you would add to the `--nodelist` argument.
To reproduce results on the local machine, change it to `Local` instead.
Then, run:

```
cargo run -r load experiments/mbkp
cargo run -r load experiments/mbkp-control
cargo run -r load experiments/mbssp
cargo run -r load experiments/mbssp-control
```

For any questions, please email me at `henk.bierlee@kuleuven.be`

Kind regards,

Hendrik 'Henk' Bierlee

