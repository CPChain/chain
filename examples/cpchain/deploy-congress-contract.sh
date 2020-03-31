#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

../../build/bin/contract-admin congress deploy --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501

# password: password

# test update congress
# ../../build/bin/contract-admin congress setperiod 0 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
# ../../build/bin/contract-admin congress setversion 2 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
# ../../build/bin/contract-admin congress setthreshold 300000000000000000000000 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
# ../../build/bin/contract-admin congress showconfigs --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
# ../../build/bin/contract-admin congress showcongress --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# test members join and quit congress
# ../../build/bin/contract-admin congress join --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
# ../../build/bin/contract-admin congress quit --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
