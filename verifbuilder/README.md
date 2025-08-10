# Подготовка

Для конкретной машины **делается один раз**.

```bash
python3 -m pip install -r requirements.txt --user
```

# Тест

```bash
# Test builder
python3 -B run.py --tool=questa --out=./new/out/ --tool=questa --seed=12345 --testlist=./example/testlist.yaml --rtl_sim=./example/rtl_simulation.yaml --tests base_test custom_test --iters=1 --rlog=./new/out/regr.log  --rexp "UVM_ERROR :    0" "UVM_FATAL :    0" --iters=6 --batch -j3
```