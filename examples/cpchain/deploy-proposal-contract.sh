#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

../../build/bin/contract-admin proposal deploy 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501

# password: password

# contract address: 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# submit
# ../../build/bin/contract-admin proposal submit --id 18a5281f-f466-45aa-ac72-88e5449cfa3b --period 1 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
# ../../build/bin/contract-admin proposal submit --id 78a5281f-f466-45aa-ac72-88e5449cfa3b --period 1 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# show configs
# ../../build/bin/contract-admin proposal show-configs --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# set amount threshold
# ../../build/bin/contract-admin proposal set-amount-threshold 1000000000000000000 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# set approval threshold
# ../../build/bin/contract-admin proposal set-approval-threshold 3 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# set vote threshold
# ../../build/bin/contract-admin proposal set-vote-threshold 30 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# set maxIDLength
# ../../build/bin/contract-admin proposal set-max-id-length 30 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# set maxPeriod
# ../../build/bin/contract-admin proposal set-max-period 30 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# disable
# ../../build/bin/contract-admin proposal disable --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# enable
# ../../build/bin/contract-admin proposal enable --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# refund
# ../../build/bin/contract-admin proposal refund --id 18a5281f-f466-45aa-ac72-88e5449cfa3b --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0
# ../../build/bin/contract-admin proposal refund --id 78a5281f-f466-45aa-ac72-88e5449cfa3b --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

# refundAll, need disable before call this
# ../../build/bin/contract-admin proposal refund-all --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x3355B3510aF6BffE670a3a8480D87dE173aB27c0

