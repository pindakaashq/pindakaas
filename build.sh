#!/usr/bin/env bash
set -e

echo "Checking installation of MiniZinc (>=2.8.3) and availability on PATH. If error, install MiniZinc manually."
minizinc --version

root=$(pwd)

if [[ ! -d "./bin/cadical/build" ]]; then
	cd ./bin/cadical/
	./configure && make
	cd ../..
fi

if [[ ! -d "./bin/mkplot/venv" ]]; then
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

	cp picat.msc.in "$solvers/picat.msc"
	cd $solvers

        cd $root
        
	echo "var 1..10: x; constraint x >= 5;" | $minizinc --solver bin/solvers/picat.msc --fzn ./bin/Picat/knapsack.picat.fzn -c -
        cat ./bin/Picat/knapsack.picat.fzn
        ./bin/Picat/picat ./bin/Picat/fzn_picat/fzn_picat_sat.pi -e ./bin/Picat/knapsack.picat.dimacs ./bin/Picat/knapsack.picat.fzn
        cat ./bin/Picat/knapsack.picat.dimacs
fi

cargo check

