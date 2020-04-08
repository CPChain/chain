#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

../../build/bin/contract-admin congress deploy --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501

# password: password

# test update congress
# ../../build/bin/contract-admin congress setperiod 0 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388
# ../../build/bin/contract-admin congress setversion 2 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388
# ../../build/bin/contract-admin congress setthreshold 300000000000000000000000 --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388
# ../../build/bin/contract-admin congress showconfigs --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388
# ../../build/bin/contract-admin congress showcongress --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388

# test members join and quit congress
# ../../build/bin/contract-admin congress join --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388
# ../../build/bin/contract-admin congress quit --keystore data/data21/keystore/ --endpoint http://127.0.0.1:8501 --contractaddr 0x00346b4805D009b8e6FEaD10F9AD371c4fB9d388
