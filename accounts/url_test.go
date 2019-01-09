// Copyright 2018 The cpchain authors

package accounts

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestURL_CmpTrue(t *testing.T) {
	t.Parallel()
	url1 := URL{Scheme: "http", Path: "aaa/bbb"}
	url2 := URL{Scheme: "http", Path: "aaa/bbb"}
	assert.Equal(t, 0, url1.Cmp(url2))
}

func TestURL_CmpFalse(t *testing.T) {
	t.Parallel()
	url1 := URL{Scheme: "http", Path: "aaa/bbb"}
	url2 := URL{Scheme: "http", Path: "aaa/bbb1"}
	assert.NotEqual(t, 0, url1.Cmp(url2))
}

func TestURL_CmpFalse1(t *testing.T) {
	t.Parallel()
	url1 := URL{Scheme: "ftp", Path: "aaa/bbb"}
	url2 := URL{Scheme: "http", Path: "aaa/bbb1"}
	assert.Equal(t, -1, url1.Cmp(url2))
}

func TestURL_MarshalJSON(t *testing.T) {
	t.Parallel()
	url1 := URL{Scheme: "http", Path: "aaa/bbb"}
	jsonBytes, err := json.Marshal(url1)
	assert.Nil(t, err)
	assert.Equal(t, "\"http://aaa/bbb\"", string(jsonBytes))
}

func TestURL_String(t *testing.T) {
	t.Parallel()
	url1 := URL{Scheme: "", Path: "aaa/bbb"}
	assert.Equal(t, "aaa/bbb", url1.String())
}

func TestURL_UnmarshalJSON(t *testing.T) {
	t.Parallel()
	url1 := URL{Scheme: "http", Path: "aaa/bbb"}
	jsonBytes, err := json.Marshal(url1)
	assert.Nil(t, err)
	assert.Equal(t, "\"http://aaa/bbb\"", string(jsonBytes))

	var url2 URL
	err = json.Unmarshal(jsonBytes, &url2)
	assert.Nil(t, err)
	assert.Equal(t, 0, url1.Cmp(url2))
}

func TestURL_UnmarshalJSON2(t *testing.T) {
	t.Parallel()

	var url3 URL
	err := json.Unmarshal([]byte("bbb"), &url3)
	assert.NotNil(t, err)
}

func TestParseUrlOk(t *testing.T) {
	t.Parallel()
	url, err := parseURL("http://aaa/bbb/ccc")
	assert.Nil(t, err)
	assert.Equal(t, "http://aaa/bbb/ccc", url.String())
}

func TestParseUrlFail(t *testing.T) {
	t.Parallel()
	url, err := parseURL("//aaa/bbb/ccc")
	assert.NotNil(t, err)
	assert.Equal(t, "", url.String())

	url, err = parseURL("/aaa/bbb/ccc")
	assert.NotNil(t, err)
	assert.Equal(t, "", url.String())
}

func TestURL_TerminalString1(t *testing.T) {
	t.Parallel()
	url, err := parseURL("http://aaa/bbb/cccccdddddeeeeefffffgggggjjjjjkkkkk")
	assert.Nil(t, err)
	assert.Equal(t, "http://aaa/bbb/cccccdddddeeeeef…", url.TerminalString())
}

func TestURL_TerminalString2(t *testing.T) {
	t.Parallel()
	url, err := parseURL("http://aaa/bbb/cccccddddde")
	assert.Nil(t, err)
	assert.Equal(t, "http://aaa/bbb/cccccddddde", url.TerminalString())
}
