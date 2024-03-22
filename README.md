# PBC/Pindakaas for reproducing CPAIOR'24, "Single Constant Multiplication for SAT"

Hendrik Bierlee, Jip J. Dekker, Vitaly Lagoon, Peter J. Stuckey, Guido Tack

Corresponding author: Hendrik 'Henk' Bierlee (hendrik.bierlee@monash.edu)

Dependencies:

- Rust >= 1.75 (for main implementation)
- Python >=3 (for plotting)
- MiniZinc >=2.8 (available on PATH)
- Slurm (optional)

Results from the paper are in `scm-full.zip`

The experiments can be run locally by changing the nodelist to "Local" in "./experiments/scm-full/slurm.json", otherwise they are executed on slurm with `--nodelist critical001` (requires a small change in `src/slurm.rs` to change this nodelist name). Once this is done, run and analyze these commands:

```
chmod +x ./build.sh
./build.sh
cargo run --release load ./experiments/scm-full/slurm.json

# after experiments are done, check and plot:
cargo run analyze --check --plot ./experiments/scm-full
```

Note: Picat-SAT will be downloaded for Linux by the build scripts
