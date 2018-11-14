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

package log

import (
	"io"

	"github.com/Sirupsen/logrus"
)

var (
	root           = New()
	termTimeFormat = "01-02|15:04:05.000"
)

// ShowFilename show filename and position
func ShowFilename() {
	root.skip()
	root.ShowFilename()
}

func Root() *Logger {
	return root
}

func getFields(ctx ...interface{}) logrus.Fields {
	fields := make(logrus.Fields, len(ctx))
	for i := 0; i < len(ctx); i += 2 {
		k, ok := ctx[i].(string)
		if !ok {
			return nil
		}
		fields[k] = ctx[i+1]
	}
	return fields
}

// SetLevel sets the logger level.
func SetLevel(level logrus.Level) {
	root.SetLevel(level)
}

// GetLevel returns the logger level.
func GetLevel() logrus.Level {
	return root.GetLevel()
}

// SetOutput sets the logger output.
func SetOutput(output io.Writer) {
	root.SetOutput(output)
}

// SetFormatter sets the logger formatter.
func SetFormatter(formatter logrus.Formatter) {
	root.SetFormatter(formatter)
}

// Info logs a message at level Info on the standard logger.
func Info(msg string, ctx ...interface{}) {
	root.Info(msg, ctx...)
}

// Print logs a message at level Info on the standard logger.
func Print(msg string, ctx ...interface{}) {
	root.Print(msg, ctx...)
}

// Debug logs a message at level Debug on the standard logger.
func Debug(msg string, ctx ...interface{}) {
	root.Debug(msg, ctx...)
}

// Warn logs a message at level Warn on the standard logger.
func Warn(msg string, ctx ...interface{}) {
	root.Warn(msg, ctx...)
}

// Error logs a message at level Error on the standard logger.
func Error(msg string, ctx ...interface{}) {
	root.Error(msg, ctx...)
}

// Panic logs a message at level Panic on the standard logger.
func Panic(msg string, ctx ...interface{}) {
	root.Panic(msg, ctx...)
}

// Fatal logs a message at level Fatal on the standard logger then the process will exit with status set to 1.
func Fatal(msg string, ctx ...interface{}) {
	root.Fatal(msg, ctx...)
}

// Debugf logs a message at level Debug on the standard logger.
func Debugf(format string, args ...interface{}) {
	root.Debugf(format, args...)
}

// Printf logs a message at level Info on the standard logger.
func Printf(format string, args ...interface{}) {
	root.Printf(format, args...)
}

// Infof logs a message at level Info on the standard logger.
func Infof(format string, args ...interface{}) {
	root.Infof(format, args...)
}

// Warnf logs a message at level Warn on the standard logger.
func Warnf(format string, args ...interface{}) {
	root.Warnf(format, args...)
}

// Warningf logs a message at level Warn on the standard logger.
func Warningf(format string, args ...interface{}) {
	root.Warningf(format, args...)
}

// Errorf logs a message at level Error on the standard logger.
func Errorf(format string, args ...interface{}) {
	root.Errorf(format, args...)
}

// Panicf logs a message at level Panic on the standard logger.
func Panicf(format string, args ...interface{}) {
	root.Panicf(format, args...)
}

// Fatalf logs a message at level Fatal on the standard logger then the process will exit with status set to 1.
func Fatalf(format string, args ...interface{}) {
	root.Fatalf(format, args...)
}

// Debugln logs a message at level Debug on the standard logger.
func Debugln(args ...interface{}) {
	root.Debugln(args...)
}

// Println logs a message at level Info on the standard logger.
func Println(args ...interface{}) {
	root.Println(args...)
}

// Infoln logs a message at level Info on the standard logger.
func Infoln(args ...interface{}) {
	root.Infoln(args...)
}

// Warnln logs a message at level Warn on the standard logger.
func Warnln(args ...interface{}) {
	root.Warnln(args...)
}

// Warningln logs a message at level Warn on the standard logger.
func Warningln(args ...interface{}) {
	root.Warningln(args...)
}

// Errorln logs a message at level Error on the standard logger.
func Errorln(args ...interface{}) {
	root.Errorln(args...)
}

// Panicln logs a message at level Panic on the standard logger.
func Panicln(args ...interface{}) {
	root.Panicln(args...)
}

// Fatalln logs a message at level Fatal on the standard logger then the process will exit with status set to 1.
func Fatalln(args ...interface{}) {
	root.Fatalln(args...)
}
