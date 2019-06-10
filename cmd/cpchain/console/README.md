# Console
**console** is a command-line management tool mainly used by miners.  

## Usage
**console**  [global options] **command** [command options] [arguments...] 

## Commands
### Overview
- **miner**    
Miner operations
- **rnode**   
Reward contract operations
- **status**      
Show status of cpchain node
- **help, h**    
Shows a list of commands or help for one command

### Command 'miner'
Usage: console **miner** <subcommand\> [command options] [arguments...]

#### Subcommands
- **start**  Start mining
- **stop**   Stop mining

#### OPTIONS
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")
   

### Command 'rnode'
Usage: console **rnode-quit** <subcommand\> [command options] [arguments...]
 
Quit from rnode,get lockedDeposit from fundraising account .

#### Options
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")
- **--gasprice value**  Gas Price, default 10 (default: 10)
- **--gaslimit value**  Gas Limit, default 2000000 (default: 2000000)

### Command 'status'
Usage: console **status** [command options]

Show status of the node.

#### Options
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")

### Command 'help'
Usage: console **help** 

Show help information.