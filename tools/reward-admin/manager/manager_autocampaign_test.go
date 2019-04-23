package manager_test

import (
	"context"
	"fmt"
	"io/ioutil"
	"os"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/tools/reward-admin/manager"
	out "bitbucket.org/cpchain/chain/tools/reward-admin/output"
)


func TestAutoCampaign(t *testing.T) {
	t.Skip()
	for i:=0;i<6;i++{
		executeNewRaise()
		executeNewRound()
		time.Sleep(time.Minute)
	}

}

func executeNewRaise() {
	raisename:="../../../tools/reward-admin/time_startnewraise.txt"
	if(!exists(raisename)){
		newRaise()
	}else{
		content,_:=ioutil.ReadFile(raisename)
		pastTime:=string(content)
		currentTime:=time.Now()
		m1,_:=time.ParseDuration("-3m")
		startNewRaiseTime :=currentTime.Add(m1).Format("2006-01-02 15:04")

		if(pastTime== startNewRaiseTime){
			newRaise()
		}else{
			return
		}
	}

}

func executeNewRound() {
	roundname:="../../../tools/reward-admin/time_startnewround.txt"
	if(!exists(roundname)){
		newRound()
	}else{
		content,_:=ioutil.ReadFile(roundname)
		pastTime:=string(content)
		currentTime:=time.Now()
		m2,_:=time.ParseDuration("-3m")
		startNewRoundTime :=currentTime.Add(m2).Format("2006-01-02 15:04")

		if(pastTime== startNewRoundTime){
			newRound()
		}else{
			return
		}
	}

}

func newRaise() error {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://127.0.0.1:8501"
	kspath := "../../../examples/cpchain/data/data21/keystore/key21"
	password := "../../../examples/cpchain/conf-dev/passwords/password"

	output := out.NewLogOutput()

	manager:= manager.NewConsole(&ctx, endPoint, kspath, password, &output)
	manager.StartNewRaise()
	name:="../../../tools/reward-admin/time_startnewraise.txt"
	content:= time.Now().Format("2006-01-02 15:04")
	data:=[]byte(content)
	if !manager.IsLocked() {
		err := ioutil.WriteFile(name, data, 0644)
		if err == nil {
			fmt.Println("Write newraisetime is successful!", content)
			return nil
		} else {
			return err
		}
	}
	return nil
}
func setPeriod(){
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://127.0.0.1:8501"
	kspath := "../../../examples/cpchain/data/data21/keystore/key21"
	password := "../../../examples/cpchain/conf-dev/passwords/password"

	output := out.NewLogOutput()

	manager := manager.NewConsole(&ctx, endPoint, kspath, password, &output)
	manager.SetPeriod()
}
func newRound() error{
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://127.0.0.1:8501"
	kspath := "../../../examples/cpchain/data/data21/keystore/key21"
	password := "../../../examples/cpchain/conf-dev/passwords/password"

	output := out.NewLogOutput()

	manager := manager.NewConsole(&ctx, endPoint, kspath, password, &output)
	//manager.SetPeriod()
	manager.StartNewRound()
	name:="../../../tools/reward-admin/time_startnewround.txt"
	content:= time.Now().Format("2006-01-02 15:04")
	data:=[]byte(content)
	if !manager.IsLocked() {
		err := ioutil.WriteFile(name, data, 0644)
		if err == nil {
			fmt.Println("Write newroundtime is successful!", content)
			return nil
		} else {
			return err
		}
	}
	return nil
}

func exists(path string) bool {
	_, err := os.Stat(path)    //os.Stat:to get information from a file
	if err != nil {
		if os.IsExist(err) {
			return true
		}
		return false
	}
	return true
}

