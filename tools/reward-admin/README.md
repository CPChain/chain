# Reward-admin
**reward-admin** is a command-line management tool mainly used by contract managers.  

## Usage
**reward-admin**  [global options] **command** [command options] [arguments...] 

## Commands
### Overview
- **start-new-raise**  
Open a new round of fundraising
- **start-new-round**    
Open a new round of lockup period
- **auto-campaign**   
Achieve to open a new round of fundraising and a new round of lockup period automatically
- **status**      
Show status of all users
- **help, h**    
Shows a list of commands or help for one command


### Command 'start-new-raise'
Usage: reward-admin **start-new-raise** [command options] [arguments...]

#### OPTIONS
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")


### Command 'start-new-round'
Usage: reward-admin **start-new-round** [command options] [arguments...]

#### OPTIONS
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")
   

### Command 'auto-campaign'
Usage: reward-admin **auto-campaign**  [command options] [arguments...]

#### Options
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")

### Command 'status'
Usage: reward-admin **status** [command options]

Show status of the all users.

#### Options
- **--rpc value**       Set the APIs offered over the HTTP-RPC interface (default: "http://127.0.0.1:8501")
- **--password value**  Password file to use for non-interactive password input (default: "/<home path>/.cpchain/password")
- **--keystore value**  Keystore directory (default: "/<home path>/.cpchain/keystore/")

### Command 'help'
Usage: reward-admin **help** 

Show help information.


#Add crontab commands in ubuntu:
1.# Crontab service start
Ubuntu 16.04 default Cron, if not, then install：
$sudo apt install cron

Checkout the cron service is started or not：
$pgrep cron
if print is "pid"，for example: 883， cron service is already started.
if it is no input at all,then cron service is not starting yet,it need manually startup.

$service cron start

2.# Set up a scheduled task, edit a scheduled task for the user file ; defaults to the current user :
$crontab -e 
choose number 3
  
3.# Add a task Command:
50 23 * * * ./reward-admin auto-campaign NewRaise --password cpchain/conf-dev/passwords/password --keystore cpchain/data/data21/keystore/key21 --rpc http://127.0.0.1:8501
50 23 * * * ./reward-admin auto-campaign NewRound --password cpchain/conf-dev/passwords/password --keystore cpchain/data/data21/keystore/key21 --rpc http://127.0.0.1:8501
    