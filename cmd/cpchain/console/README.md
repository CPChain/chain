# Console
**campaign** is a command-line management tool mainly used by miners.

## Usage
**campaign**  [global options] **command** [command options] [arguments...]

## Commands
### Overview
- **campaign**
Campaign operations
- **help, h**
Shows a list of commands or help for one command

### Command 'miner'
Usage: cpchain **campaign** <subcommand\> [command options] [arguments...]

#### Subcommands
- **start**  Start mining
- **stop**   Stop mining, quit from rnode,get lockedDeposit from fundraising account .
- **status**  Show status of the node.

#### OPTIONS
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")
   

#### Options
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")
- **--gasprice value**  Gas Price, default 10 (default: 10)
- **--gaslimit value**  Gas Limit, default 2000000 (default: 2000000)
- **--runmode value**   runmode, default mainnet


#### Options
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")

### Command 'help'
Usage: cpchain campaign **help**

Show help information.