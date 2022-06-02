pip install -r requirements.txt
git submodule update --init --recursive
if [ ! -f external/EvalMaxSAT/build/EvalMaxSAT_bin ];
then
	cd external/EvalMaxSAT
	mkdir build
	cd build
	cmake ..
	make
	cd ../../..
fi
