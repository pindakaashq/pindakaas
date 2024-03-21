#!/usr/bin/env bash
set -e

echo "Checking installation of MiniZinc (>=2.8.3) and availability on PATH. If error, install MiniZinc manually."
minizinc --version

root=$(pwd)
mkdir -p bin

if [[ -d ".git" ]]; then
	echo "skipping pull"
	# git pull
	#git log --oneline  @{1}..
	# git -C ./bin/pindakaas checkout feature/refactor-linear-encoding
	# git -C ./bin/pindakaas pull 
	#git -C ./bin/pindakaas log --oneline  @{1}..
fi

if [[ ! -d "./bin/pindakaas" ]]; then
  cd bin
  git clone git@github.com:pindakaashq/pindakaas.git -b feature/refactor-linear-encoding
  cargo check
  cd ..
fi

if [[ ! -d "./bin/cadical" ]]; then
  cd bin
  git clone --depth 1 --branch rel-1.9.1 https://github.com/arminbiere/cadical.git
  cd ..
fi

if [[ ! -d "./bin/cadical/build" ]]; then
	cd ./bin/cadical/
	./configure && make
	cd ../..
fi

# if [[ ! -d "./bin/fun-scop" ]]; then
#   cd bin
#   wget https://tsoh.org/sCOP/scop-for-xcsp18-180731.tar.gz
#   tar -xf scop-for-xcsp18-180731.tar.gz
#   rm scop-for-xcsp18-180731.tar.gz
#   cd ..
# fi

if [[ ! -d "./bin/pblib" ]]; then
	cd ./bin/pblib
	chmod +x ./build.sh
	./build.sh
	cd ../..
fi

if [[ ! -d "./bin/mkplot" ]]; then
        mkdir bin/mkplot
	cd ./bin/mkplot
	python -m venv venv
	source ./venv/bin/activate
	pip install matplotlib
	cd ../..
fi


if [ ! -d "./bin/Picat" ] ; then
        cd ./bin
	wget http://picat-lang.org/download/picat35_linux64.tar.gz
	tar -xf picat35_linux64.tar.gz 
	rm picat35_linux64.tar.gz
	cd Picat
	git clone git@github.com:nfzhou/fzn_picat.git
	cd fzn_picat
	cat << EOF > picat.sh
#!
exec $root/bin/Picat/picat -path $root/bin/Picat/fzn_picat fzn_picat_sat.pi "\$@"
EOF
	chmod +x picat.sh

        cp $root/picat.diff ./
        git apply picat.diff

        solvers="$root/bin/solvers"
        mkdir -p $solvers

        minizinc="minizinc"
        echo "{ \"mzn_solver_path\": [\"$root/bin/solvers\"] }" > $HOME/.minizinc/Preferences.json

	cp picat.msc.in "$solvers/picat.msc"
	cd $solvers

        cd $root
        
	echo "var 1..10: x; constraint x >= 5;" | $minizinc --solver picat --fzn ./bin/Picat/knapsack.picat.fzn -c -
        cat ./bin/Picat/knapsack.picat.fzn
        ./bin/Picat/picat ./bin/Picat/fzn_picat/fzn_picat_sat.pi -e ./bin/Picat/knapsack.picat.dimacs ./bin/Picat/knapsack.picat.fzn
        cat ./bin/Picat/knapsack.picat.dimacs
fi

cargo build --release

exp="./experiments/rand-eqs-a"

cat << EOF
- Build successful; run \`cargo run --release load \`$exp/slurm.json\` to reproduce experiments.
- Savile Row 1.9.2 is not included as it is not released at the time of writing. If it is not available in ./bin/savilerow_1.9.2, remove SavileRow from \`$exp\slurm.json\`.
- Change the nodelist field in slurm.json to \`Local\` to run locally if no slurm cluster is available.
- After completion (or to analyze run logs in $exp shown in the manuscript), run \`cargo run --release analyze $exp --check --plot\` to check solutions, plot results and compile csv.
EOF

