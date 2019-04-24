package main

import (
	"fmt"
	"io/ioutil"
	"os"
	"os/user"
	"path/filepath"
	"runtime"
	"time"

	"github.com/urfave/cli"
	"bitbucket.org/cpchain/chain/commons/log"
)


var autocampaignCommand cli.Command

func init() {
	defaultname:=DefaultDataDir()
	recordfile:=filepath.Join(defaultname,"record.txt")
	f, err := os.OpenFile(recordfile, os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0644)
	if err == nil {
		log.SetOutput(f)
	}
	rewardFlags := append([]cli.Flag(nil))
	autocampaignCommand = cli.Command{
		Name:   "auto-campaign",
		Flags:  wrapperFlags(rewardFlags),
		Usage:  "Reward contract AutoCampaign",
		Subcommands: []cli.Command{
			{
				Name:        "NewRaise",
				Usage:       "Contract manager start next fundraise",
				Flags:       wrapperFlags(rewardFlags),
				Action:      ExecuteNewRaise,
			},
			{
				Name:        "NewRound",
				Usage:       "Contract manager start next round",
				Flags:       wrapperFlags(rewardFlags),
				Action:      ExecuteNewRound,
			},
		},
	}

}


func ExecuteNewRaise(ctx *cli.Context) {
	defaultname:=DefaultDataDir()
	raisename:=filepath.Join(defaultname,"newRaise.txt")
	content,_:=ioutil.ReadFile(raisename)
	pastTime:=string(content)
	currentTime:=time.Now()
	startNewRaiseTime :=currentTime.AddDate(0,0,-90).Format("2006-01-02")
	log.Info("======= start@"+currentTime.Format("2006-01-02")+" =========")

	defer func() {
		log.Info("============== end ===============")
		log.Info("")
		log.Info("")
	}()
	if(!Exists(raisename)){
		NewRaise(ctx)
	}else{
		if(pastTime== startNewRaiseTime){
			NewRaise(ctx)
		}else{
			log.Info("to startnewraise is not correct time!")
			return
		}
	}
}

func ExecuteNewRound(ctx *cli.Context) {
	defaultname:=DefaultDataDir()
	roundname:=filepath.Join(defaultname,"newRound.txt")
	content,_:=ioutil.ReadFile(roundname)
	pastTime:=string(content)
	currentTime:=time.Now()
	startNewRoundTime :=currentTime.AddDate(0,0,-90).Format("2006-01-02")
	log.Info("======= start@"+currentTime.Format("2006-01-02")+" =========")

	defer func() {
		log.Info("============== end ===============")
		log.Info("")
		log.Info("")
	}()

	if(!Exists(roundname)){
		NewRound(ctx)
	}else{

		if(pastTime== startNewRoundTime){
			NewRound(ctx)
		}else{
			log.Info("to startnewround is not correct time!")
			return
		}
	}

}

func NewRound(ctx *cli.Context) error {
	admin, out, cancel := Build(ctx)
	defer cancel()
	err := admin.StartNewRound()
	if err != nil {
		out.Error(err.Error())
		log.Error(err.Error())
		return err
	}
	defaultname:=DefaultDataDir()
	name:=filepath.Join(defaultname,"newRound.txt")
	content:= time.Now().Format("2006-01-02")
	data:=[]byte(content)
	if admin.IsLocked() {
		err1 := ioutil.WriteFile(name, data, 0644)
		if err1 == nil {
			mark:="Write newroundtime is successful! and the time is "+content
			fmt.Println(mark)
			log.Info(mark)
		} else {
			log.Error(err1.Error())
			return err1
		}
	}
	return nil
}

func NewRaise(ctx *cli.Context) error {
	admin, out, cancel := Build(ctx)
	defer cancel()
	err := admin.StartNewRaise()
	if err != nil {
		out.Error(err.Error())
		log.Error(err.Error())
		return err
	}
	defaultname:=DefaultDataDir()
	name:=filepath.Join(defaultname,"newRaise.txt")
	content:= time.Now().Format("2006-01-02")
	data:=[]byte(content)
	if !admin.IsLocked() {
		err1 := ioutil.WriteFile(name, data, 0644)
		if err1 == nil {
			mark:="Write newraisetime is successful! and the time is "+content
			fmt.Println(mark)
			log.Info( mark)
		} else {
			log.Error(err1.Error())
			return err1
		}
	}
	return nil
}


func Exists(path string) bool {
	_, err := os.Stat(path)    //os.Stat:to get information from a file
	if err != nil {
		if os.IsExist(err) {
			return true
		}
		return false
	}
	return true
}

func DefaultDataDir() string {
	// Try to place the data folder in the user's home dir
	home := homeDir()
	if home != "" {
		if runtime.GOOS == "darwin" {
			return filepath.Join(home, "Library", "Cpchain")
		} else if runtime.GOOS == "windows" {
			return filepath.Join(home, "AppData", "Roaming", "Cpchain")
		} else {
			return filepath.Join(home, ".cpchain")
		}
	}
	// As we cannot guess a stable location, return empty and handle later
	return ""
}

func homeDir() string {
	if home := os.Getenv("HOME"); home != "" {
		return home
	}
	if usr, err := user.Current(); err == nil {
		return usr.HomeDir
	}
	log.Println("No home directory found")
	return ""
}
