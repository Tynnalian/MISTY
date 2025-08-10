# Определение переменных


MERGED_COVERAGE_FILE = ../../../../cov/RP_plan.ucdb
COVERAGE_EXCLUDE_DO = ../cov/coverage_exclude.do
WAVE_DO = ./wave.do

TESTS = test_base
RESETS = 0
GUI = 1
SEED = 10
ITERS=1

# Условное определение переменной GUI_BATCH
ifeq ($(GUI),1)
	GUI_BATCH := --gui
else
	GUI_BATCH := --batch
endif

# Правило для компиляции и симуляции файлов с помощью Verifbuilder
sim_fraim:
	python3 -B ../../../../../verifbuilder/run.py --tool=questa --out=./new/out/ --rtl_sim=rtl_simulation.yaml \
	--testlist=testlist.yaml  --tests $(TESTS) --seed=$(SEED) \
	--rlog=./new/out/regr.log --rexp "UVM_ERROR :    0" "UVM_FATAL :    0" "Errors: 0" --iters=$(ITERS) -j128 $(GUI_BATCH)

# Правило для объединения покрытия
merge_cov:
	vcover merge $(MERGED_COVERAGE_FILE) $(MERGED_COVERAGE_FILE) new/out/*.ucdb
	vsim -viewcov $(MERGED_COVERAGE_FILE) 


# Правило для очистки c помощью Verifbuilder
clean_fraim:
	python3 -B ../../../../../verifbuilder/run.py --tool=questa --out=./new/ --clean 



