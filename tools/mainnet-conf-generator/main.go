package main

import (
	"fmt"
	"html/template"
	"os"

	"bitbucket.org/cpchain/chain/tools/mainnet-conf-generator/temp"
)

func main() {

	err := RunTemplate(temp.Config_mainnet, temp.Mc01)
	if err != nil {
		fmt.Println("Template Failed!")
	}
}

func RunTemplate(c string, mc temp.MainnetConfig) error {
	tmpl, err := template.New("mainnet_config").Parse(c)
	if err != nil {
		return err
	}
	err = tmpl.Execute(os.Stdout, mc)
	if err != nil {
		return err
	}
	return nil
}
