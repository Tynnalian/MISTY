NAME=MISTY

sim: build/libpysv.so
	vlib work
	vmap work
	vlog -sv pysv_pkg.sv $(NAME)_top.sv
	vsim -64 $(NAME)_top -sv_lib build/libpysv -do "run -a;"

clean:
	@rm -rf build work __pycache__
	@rm -f transcript vsim_stacktrace.vstf pysv_pkg.sv
	
build/libpysv.so: clean
	python3 models.py