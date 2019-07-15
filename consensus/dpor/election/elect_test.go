// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package election

import (
	"math/big"
	"math/rand"
	"os"
	"reflect"
	"strconv"
	"testing"

	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"github.com/ethereum/go-ethereum/common"
)

func Test_findHit(t *testing.T) {
	type args struct {
		hit     int64
		hitSums []int64
	}
	tests := []struct {
		name string
		args args
		want int
	}{
		// TODO: Add test cases.
		{
			name: "0",
			args: args{
				hit:     13,
				hitSums: []int64{1, 4, 8, 15},
			},
			want: 3,
		},
		{
			name: "1",
			args: args{
				hit:     1,
				hitSums: []int64{1, 4, 8, 15},
			},
			want: 0,
		},
		{
			name: "2",
			args: args{
				hit:     2,
				hitSums: []int64{1, 4, 8, 15},
			},
			want: 1,
		},
		{
			name: "3",
			args: args{
				hit:     16,
				hitSums: []int64{1, 4, 8, 15},
			},
			want: 3,
		},
		{
			name: "4",
			args: args{
				hit:     9,
				hitSums: []int64{1, 4, 8, 15},
			},
			want: 3,
		},
		{
			name: "5",
			args: args{
				hit:     7,
				hitSums: []int64{1, 4, 8, 15},
			},
			want: 2,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := findHit(tt.args.hit, tt.args.hitSums); got != tt.want {
				t.Errorf("findHit() = %v, want %v", got, tt.want)
			}
		})
	}
}

func Test_sumOfFirstN(t *testing.T) {
	type args struct {
		rpts rpt.RptList
	}
	tests := []struct {
		name     string
		args     args
		wantSums []int64
		wantSum  int64
	}{
		// TODO: Add test cases.
		{
			name: "1",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(3)),
					},
					rpt.Rpt{
						Rpt:     4,
						Address: common.BigToAddress(big.NewInt(4)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(7)),
					},
				},
			},
			wantSums: []int64{1, 4, 8, 15},
			wantSum:  15,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			gotSums, gotSum := sumOfFirstN(tt.args.rpts)
			if !reflect.DeepEqual(gotSums, tt.wantSums) {
				t.Errorf("sumOfFirstN() gotSums = %v, want %v", gotSums, tt.wantSums)
			}
			if gotSum != tt.wantSum {
				t.Errorf("sumOfFirstN() gotSum = %v, want %v", gotSum, tt.wantSum)
			}
		})
	}
}

func Test_randomSelectByRpt(t *testing.T) {
	type args struct {
		rpts   rpt.RptList
		myRand *rand.Rand
		seats  int
	}
	tests := []struct {
		name       string
		args       args
		wantResult []common.Address
	}{
		// TODO: Add test cases.
		{
			name: "1",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(3)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(7)),
					},
					rpt.Rpt{
						Rpt:     4,
						Address: common.BigToAddress(big.NewInt(4)),
					},
				},
				myRand: rand.New(rand.NewSource(1)),
				seats:  2,
			},
			wantResult: []common.Address{
				common.BigToAddress(big.NewInt(4)),
				common.BigToAddress(big.NewInt(1)),
			},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotResult := randomSelectByRpt(tt.args.rpts, tt.args.myRand, tt.args.seats); !reflect.DeepEqual(gotResult, tt.wantResult) {
				t.Errorf("randomSelectByRpt() = %v, want %v", gotResult, tt.wantResult)
			}
		})
	}
}

func TestElect2(t *testing.T) {
	type args struct {
		rpts         rpt.RptList
		seed         int64
		totalSeats   int
		lowRptCounts int
		lowRptSeats  int
	}
	tests := []struct {
		name string
		args args
		want []common.Address
	}{
		// TODO: Add test cases.

		{
			name: "1",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(2)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(3)),
					},
					rpt.Rpt{
						Rpt:     2,
						Address: common.BigToAddress(big.NewInt(4)),
					},
					rpt.Rpt{
						Rpt:     5,
						Address: common.BigToAddress(big.NewInt(5)),
					},
					rpt.Rpt{
						Rpt:     9,
						Address: common.BigToAddress(big.NewInt(6)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(7)),
					},
					rpt.Rpt{
						Rpt:     12,
						Address: common.BigToAddress(big.NewInt(8)),
					},
					rpt.Rpt{
						Rpt:     22,
						Address: common.BigToAddress(big.NewInt(9)),
					},
					rpt.Rpt{
						Rpt:     9,
						Address: common.BigToAddress(big.NewInt(10)),
					},
					rpt.Rpt{
						Rpt:     10,
						Address: common.BigToAddress(big.NewInt(11)),
					},
					rpt.Rpt{
						Rpt:     35,
						Address: common.BigToAddress(big.NewInt(12)),
					},
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(13)),
					},
					rpt.Rpt{
						Rpt:     0,
						Address: common.BigToAddress(big.NewInt(14)),
					},
					rpt.Rpt{
						Rpt:     1000,
						Address: common.BigToAddress(big.NewInt(15)),
					},
					rpt.Rpt{
						Rpt:     400,
						Address: common.BigToAddress(big.NewInt(16)),
					},
					rpt.Rpt{
						Rpt:     5,
						Address: common.BigToAddress(big.NewInt(17)),
					},
				},
				seed:         1,
				totalSeats:   8,
				lowRptCounts: 10,
				lowRptSeats:  2,
			},
			want: []common.Address{
				common.BigToAddress(big.NewInt(5)),
				common.BigToAddress(big.NewInt(7)),
				common.BigToAddress(big.NewInt(16)),
				common.BigToAddress(big.NewInt(15)),
				common.BigToAddress(big.NewInt(10)),
				common.BigToAddress(big.NewInt(8)),
				common.BigToAddress(big.NewInt(11)),
				common.BigToAddress(big.NewInt(9)),
			},
		},
		{
			name: "2",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(2)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(3)),
					},
					rpt.Rpt{
						Rpt:     2,
						Address: common.BigToAddress(big.NewInt(4)),
					},
					rpt.Rpt{
						Rpt:     5,
						Address: common.BigToAddress(big.NewInt(5)),
					},
					rpt.Rpt{
						Rpt:     9,
						Address: common.BigToAddress(big.NewInt(6)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(7)),
					},
					rpt.Rpt{
						Rpt:     12,
						Address: common.BigToAddress(big.NewInt(8)),
					},
					rpt.Rpt{
						Rpt:     22,
						Address: common.BigToAddress(big.NewInt(9)),
					},
					rpt.Rpt{
						Rpt:     9,
						Address: common.BigToAddress(big.NewInt(10)),
					},
					rpt.Rpt{
						Rpt:     10,
						Address: common.BigToAddress(big.NewInt(11)),
					},
					rpt.Rpt{
						Rpt:     35,
						Address: common.BigToAddress(big.NewInt(12)),
					},
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(13)),
					},
					rpt.Rpt{
						Rpt:     0,
						Address: common.BigToAddress(big.NewInt(14)),
					},
					rpt.Rpt{
						Rpt:     1000,
						Address: common.BigToAddress(big.NewInt(15)),
					},
					rpt.Rpt{
						Rpt:     400,
						Address: common.BigToAddress(big.NewInt(16)),
					},
					rpt.Rpt{
						Rpt:     5,
						Address: common.BigToAddress(big.NewInt(17)),
					},
				},
				seed:         1,
				totalSeats:   4,
				lowRptCounts: 10,
				lowRptSeats:  2,
			},
			want: []common.Address{
				common.BigToAddress(big.NewInt(5)),
				common.BigToAddress(big.NewInt(7)),
				common.BigToAddress(big.NewInt(16)),
				common.BigToAddress(big.NewInt(15)),
			},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := Elect(tt.args.rpts, tt.args.seed, tt.args.totalSeats, tt.args.lowRptCounts, tt.args.lowRptSeats)
			println("got===", got)
			println("want===", tt.want)
			println("reflect===", reflect.DeepEqual(got, tt.want))
			if got := Elect(tt.args.rpts, tt.args.seed, tt.args.totalSeats, tt.args.lowRptCounts, tt.args.lowRptSeats); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Elect2() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestElect_RPT(t *testing.T) { //illustrate the relationship between probability of being seleted of one node and its RPT value
	i := 0
	times := 200
	for ; i < times; i++ {
		totalSeats := 8
		lowRptCounts := 10
		lowRptSeats := 2
		rptsNew := rpt.RptList{
			rpt.Rpt{
				Rpt:     10,
				Address: common.BigToAddress(big.NewInt(1)),
			},
			rpt.Rpt{
				Rpt:     20,
				Address: common.BigToAddress(big.NewInt(2)),
			},
			rpt.Rpt{
				Rpt:     30,
				Address: common.BigToAddress(big.NewInt(3)),
			},
			rpt.Rpt{
				Rpt:     40,
				Address: common.BigToAddress(big.NewInt(4)),
			},
			rpt.Rpt{
				Rpt:     50,
				Address: common.BigToAddress(big.NewInt(5)),
			},
			rpt.Rpt{
				Rpt:     60,
				Address: common.BigToAddress(big.NewInt(6)),
			},
			rpt.Rpt{
				Rpt:     70,
				Address: common.BigToAddress(big.NewInt(7)),
			},
			rpt.Rpt{
				Rpt:     80,
				Address: common.BigToAddress(big.NewInt(8)),
			},
			rpt.Rpt{
				Rpt:     90,
				Address: common.BigToAddress(big.NewInt(9)),
			},
			rpt.Rpt{
				Rpt:     100,
				Address: common.BigToAddress(big.NewInt(10)),
			},
			rpt.Rpt{
				Rpt:     110,
				Address: common.BigToAddress(big.NewInt(11)),
			},
			rpt.Rpt{
				Rpt:     120,
				Address: common.BigToAddress(big.NewInt(12)),
			},
			rpt.Rpt{
				Rpt:     130,
				Address: common.BigToAddress(big.NewInt(13)),
			},
			rpt.Rpt{
				Rpt:     140,
				Address: common.BigToAddress(big.NewInt(14)),
			},
			rpt.Rpt{
				Rpt:     150,
				Address: common.BigToAddress(big.NewInt(15)),
			},
			rpt.Rpt{
				Rpt:     160,
				Address: common.BigToAddress(big.NewInt(16)),
			},
			rpt.Rpt{
				Rpt:     170,
				Address: common.BigToAddress(big.NewInt(17)),
			},
			rpt.Rpt{
				Rpt:     180,
				Address: common.BigToAddress(big.NewInt(18)),
			},
		}
		want := common.BigToAddress(big.NewInt(20))
		adRpt := i
		subRpt := 200 - i
		ad := rpt.Rpt{
			Rpt:     int64(adRpt),
			Address: common.BigToAddress(big.NewInt(20)),
		}
		sub := rpt.Rpt{
			Rpt:     int64(subRpt),
			Address: common.BigToAddress(big.NewInt(19)),
		}
		rpts1 := append(rptsNew, ad)
		rpts := append(rpts1, sub)

		count := 0
		randNum := rand.Intn(5000)
		sum := int64(randNum + 5000)
		seed := int64(randNum)

		for ; seed < sum; seed++ {

			got := Elect(rpts, seed, totalSeats, lowRptCounts, lowRptSeats)
			if contains(want, got) {
				count++
			}
		}

		println("rpt is ", adRpt, "the propotion of address 20 is", count)

		if i != times-1 {
			tracefile1(count)
		} else {
			tracefile2(count)
		}

	}

}

func TestPreConditionElect(t *testing.T) { //boundary value of elect function
	type args struct {
		rpts         rpt.RptList
		seed         int64
		totalSeats   int
		lowRptCounts int
		lowRptSeats  int
	}
	tests := []struct {
		name string
		args args
		want []common.Address
	}{
		// TODO: Add test cases.
		{
			name: "1",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(2)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(3)),
					},
				},
				seed:         1,
				totalSeats:   0,
				lowRptCounts: 10,
				lowRptSeats:  9,
			},
			want: []common.Address{}, //totalseat==0
		},
		{
			name: "2",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(2)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(3)),
					},
				},
				seed:         1,
				totalSeats:   7,
				lowRptCounts: 4,
				lowRptSeats:  3,
			},
			want: []common.Address{}, //lowRptCount > rpts.Len()
		},
		{
			name: "3",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(2)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(3)),
					},
				},
				seed:         7,
				totalSeats:   12,
				lowRptCounts: 10,
				lowRptSeats:  15,
			},
			want: []common.Address{}, //lowRptSeats > totalSeats
		},

		{
			name: "4",
			args: args{
				rpts: rpt.RptList{
					rpt.Rpt{
						Rpt:     1,
						Address: common.BigToAddress(big.NewInt(1)),
					},
					rpt.Rpt{
						Rpt:     3,
						Address: common.BigToAddress(big.NewInt(2)),
					},
					rpt.Rpt{
						Rpt:     7,
						Address: common.BigToAddress(big.NewInt(3)),
					},
				},
				seed:         2,
				totalSeats:   5,
				lowRptCounts: 4,
				lowRptSeats:  3,
			},
			want: []common.Address{}, //totalSeats > rpts.Len()
		},

		{
			name: "5",
			args: args{
				rpts:         rpt.RptList{},
				seed:         62736732873,
				totalSeats:   5,
				lowRptCounts: 4,
				lowRptSeats:  3,
			},
			want: []common.Address{}, //number of RPTlist is 0
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {

			if got := Elect(tt.args.rpts, tt.args.seed, tt.args.totalSeats, tt.args.lowRptCounts, tt.args.lowRptSeats); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Elect2() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestPreConditionRandomSelectByRpt(t *testing.T) { //boundary value of RandomSelectByRpt function
	type args struct {
		rpts   rpt.RptList
		myRand *rand.Rand
		seats  int
	}
	tests := []struct {
		name       string
		args       args
		wantResult []common.Address
	}{
		// TODO: Add test cases.
		{
			name: "1",
			args: args{
				rpts:   rpt.RptList{},
				myRand: rand.New(rand.NewSource(1)),
				seats:  0,
			},
			wantResult: nil,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotResult := randomSelectByRpt(tt.args.rpts, tt.args.myRand, tt.args.seats); !reflect.DeepEqual(gotResult, tt.wantResult) {
				t.Errorf("randomSelectByRpt() = %v, want %v", gotResult, tt.wantResult)
			}
		})
	}

}

func contains(a common.Address, all []common.Address) bool {
	for _, x := range all {
		if x == a {
			return true
		}
	}
	return false
}
func tracefile1(str_content int) {
	fd, _ := os.OpenFile("/tmp/cpchain_data.txt", os.O_RDWR|os.O_CREATE|os.O_APPEND, 0644)
	fd.WriteString(strconv.Itoa(str_content))
	fd.WriteString(",")
	fd.Close()
}

func tracefile2(str_content int) {
	fd, _ := os.OpenFile("/tmp/cpchain_data.txt", os.O_RDWR|os.O_CREATE|os.O_APPEND, 0644)
	fd.WriteString(strconv.Itoa(str_content))
	fd.Close()
}

func benchmarkElect(seed int64, b *testing.B) {
	rptsNew := rpt.RptList{}
	totalSeats := 8
	lowRptCounts := 50
	lowRptSeats := 4
	for i := 0; i < b.N; i++ {
		for j := 1; j < 101; j++ {
			randNum := rand.Intn(500)
			rptvalue := int64(randNum)
			ad := rpt.Rpt{
				Rpt:     rptvalue,
				Address: common.BigToAddress(big.NewInt(int64(j))),
			}
			rptsNew := append(rptsNew, ad)
			if j == 100 {
				Elect(rptsNew, seed, totalSeats, lowRptCounts, lowRptSeats)
			}
		}
	}
	b.ReportAllocs()

}

func BenchmarkElect1(b *testing.B) { benchmarkElect(1, b) }
func BenchmarkElect2(b *testing.B) { benchmarkElect(2, b) }
func BenchmarkElect3(b *testing.B) { benchmarkElect(3, b) }
func BenchmarkElect4(b *testing.B) { benchmarkElect(10, b) }
func BenchmarkElect5(b *testing.B) { benchmarkElect(30, b) }
func BenchmarkElect6(b *testing.B) { benchmarkElect(2000, b) }
