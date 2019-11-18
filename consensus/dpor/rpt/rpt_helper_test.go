package rpt

import (
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

func Test_record_countAfter(t *testing.T) {
	type fields struct {
		r []uint64
	}
	type args struct {
		outset uint64
	}
	tests := []struct {
		name   string
		fields fields
		args   args
		want   int
	}{
		// TODO: Add test cases.
		{
			name: "0",
			fields: fields{
				r: []uint64{1, 2, 3, 4, 5, 8, 10},
			},
			args: args{
				outset: 0,
			},
			want: 7,
		},
		{
			name: "1",
			fields: fields{
				r: []uint64{1, 2, 3, 4, 5, 8, 10},
			},
			args: args{
				outset: 1,
			},
			want: 6,
		},
		{
			name: "2",
			fields: fields{
				r: []uint64{1, 2, 3, 4, 5, 8, 10},
			},
			args: args{
				outset: 2,
			},
			want: 5,
		},
		{
			name: "3",
			fields: fields{
				r: []uint64{1, 2, 3, 4, 5, 8, 10},
			},
			args: args{
				outset: 10,
			},
			want: 0,
		},
		{
			name: "4",
			fields: fields{
				r: []uint64{1, 2, 3, 4, 5, 8, 10},
			},
			args: args{
				outset: 11,
			},
			want: 0,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			r := &record{
				r: tt.fields.r,
			}
			if got := r.countAfter(tt.args.outset); got != tt.want {
				t.Errorf("record.countAfter() = %v, want %v", got, tt.want)
			}
		})
	}
}

func Test_impeachHistoryImpl_addHistory(t *testing.T) {

	current := uint64(10)

	outset := outsetOf(current)
	ih := &impeachHistoryImpl{
		outset:  outset,
		latest:  outset,
		records: make(map[common.Address]*record),
	}

	addr1 := common.HexToAddress("0x01")
	addr2 := common.HexToAddress("0x02")

	ih.addHistory(addr1, 1112, true)
	ih.addHistory(addr1, 1113, true)
	ih.addHistory(addr1, 1114, false)
	ih.addHistory(addr2, 1115, false)
	ih.addHistory(addr2, 1116, true)
	ih.addHistory(addr2, 1117, true)
	ih.addHistory(addr1, 1118, true)
	ih.addHistory(addr1, 1119, false)
	ih.addHistory(addr1, 11110, true)
	ih.addHistory(addr2, 11111, false)
	ih.addHistory(addr2, 11112, true)

	t.Log("current", ih.currentNumber(),
		"outset", ih.outset,
		"addr1 impeached", ih.countHistory(addr1),
		"addr2 impeached", ih.countHistory(addr2),
	)
}
