package database

import (
	"bytes"
	"reflect"
	"testing"
)

var (
	data1 = []byte("datadatadata")
	data2 = []byte{}
	data3 = bytes.Repeat([]byte("data"), 1000)
)

func TestDummyDatabase_Get(t *testing.T) {
	type args struct {
		key []byte
	}
	tests := []struct {
		name    string
		d       *DummyDatabase
		args    args
		want    []byte
		wantErr bool
	}{
		{
			name: "case 1",
			d:    new(DummyDatabase),
			args: args{
				key: data1,
			},
			want: data1,
		},
		{
			name: "case 2",
			d:    new(DummyDatabase),
			args: args{
				key: data2,
			},
			want: data2,
		},
		{
			name: "case 3",
			d:    new(DummyDatabase),
			args: args{
				key: data3,
			},
			want: data3,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &DummyDatabase{}
			got, err := d.Get(tt.args.key)
			if (err != nil) != tt.wantErr {
				t.Errorf("DummyDatabase.Get() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DummyDatabase.Get() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestDummyDatabase_Put(t *testing.T) {
	type args struct {
		value []byte
	}
	tests := []struct {
		name    string
		d       *DummyDatabase
		args    args
		want    []byte
		wantErr bool
	}{
		{
			name: "case 1",
			d:    new(DummyDatabase),
			args: args{
				value: data1,
			},
			want: data1,
		},
		{
			name: "case 2",
			d:    new(DummyDatabase),
			args: args{
				value: data2,
			},
			want: data2,
		},
		{
			name: "case 3",
			d:    new(DummyDatabase),
			args: args{
				value: data3,
			},
			want: data3,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &DummyDatabase{}
			got, err := d.Put(tt.args.value)
			if (err != nil) != tt.wantErr {
				t.Errorf("DummyDatabase.Put() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DummyDatabase.Put() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestDummyDatabase_Discard(t *testing.T) {
	type args struct {
		key []byte
	}
	tests := []struct {
		name    string
		d       *DummyDatabase
		args    args
		wantErr bool
	}{
		{
			name: "case 1",
			d:    new(DummyDatabase),
			args: args{
				key: data1,
			},
			wantErr: false,
		},
		{
			name: "case 2",
			d:    new(DummyDatabase),
			args: args{
				key: data2,
			},
			wantErr: false,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &DummyDatabase{}
			if err := d.Discard(tt.args.key); (err != nil) != tt.wantErr {
				t.Errorf("DummyDatabase.Discard() error = %v, wantErr %v", err, tt.wantErr)
			}
		})
	}
}

func TestDummyDatabase_Has(t *testing.T) {
	type args struct {
		key []byte
	}
	tests := []struct {
		name string
		d    *DummyDatabase
		args args
		want bool
	}{
		{
			name: "case 1",
			d:    new(DummyDatabase),
			args: args{
				key: data1,
			},
			want: true,
		},
		{
			name: "case 2",
			d:    new(DummyDatabase),
			args: args{
				key: data2,
			},
			want: true,
		},
		{
			name: "case 3",
			d:    new(DummyDatabase),
			args: args{
				key: data3,
			},
			want: true,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &DummyDatabase{}
			if got := d.Has(tt.args.key); got != tt.want {
				t.Errorf("DummyDatabase.Has() = %v, want %v", got, tt.want)
			}
		})
	}
}
