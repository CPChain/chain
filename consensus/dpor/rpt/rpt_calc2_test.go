package rpt

import "testing"

func Test_impeachPunishRatio(t *testing.T) {
	type args struct {
		impeachedNumber int
	}
	tests := []struct {
		name string
		args args
		want float32
	}{
		// TODO: Add test cases.
		{
			name: "1",
			args: args{
				impeachedNumber: 0,
			},
			want: 1.,
		},
		{
			name: "2",
			args: args{
				impeachedNumber: 1,
			},
			want: 1. - 1./9,
		},
		{
			name: "3",
			args: args{
				impeachedNumber: 8,
			},
			want: 1. - float32(8)/9,
		},
		{
			name: "4",
			args: args{
				impeachedNumber: 9,
			},
			want: 0.,
		},
		{
			name: "5",
			args: args{
				impeachedNumber: 10,
			},
			want: 0.,
		},
		{
			name: "6",
			args: args{
				impeachedNumber: 1000,
			},
			want: 0.,
		},
		{
			name: "7",
			args: args{
				impeachedNumber: 10000,
			},
			want: 0.,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := impeachPunishRatio(tt.args.impeachedNumber); got != tt.want {
				t.Errorf("impeachPunishRatio() = %v, want %v", got, tt.want)
			}
		})
	}
}
