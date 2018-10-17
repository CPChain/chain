package log

import (
	"io"

	"github.com/Sirupsen/logrus"
)

var (
	root           = NewLogger()
	termTimeFormat = "01-02|15:04:05.000"
)

func NewLogger() *Logger {
	l := &Logger{
		logrus.NewEntry(logrus.New()),
	}

	l.SetFormatter(&TextFormatter{
		FullTimestamp:    true,
		QuoteEmptyFields: true,
		TimestampFormat:  termTimeFormat,
	})

	return l
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
	root.Logger.SetLevel(level)
}

// GetLevel returns the logger level.
func GetLevel() logrus.Level {
	return root.Logger.GetLevel()
}

// SetOutput sets the logger output.
func SetOutput(output io.Writer) {
	root.Logger.SetOutput(output)
}

// SetFormatter sets the logger formatter.
func SetFormatter(formatter logrus.Formatter) {
	root.Logger.SetFormatter(formatter)
}

// Info logs a message at level Info on the standard logger.
func Info(msg string, ctx ...interface{}) {
	if root.Logger.IsLevelEnabled(logrus.InfoLevel) {
		if len(ctx)%2 != 0 {
			root.Error(errCtx)
			return
		}
		root.WithFields(getFields(ctx...)).Info(msg)
	}
}

// Print logs a message at level Info on the standard logger.
func Print(msg string, ctx ...interface{}) {
	if root.Logger.IsLevelEnabled(logrus.InfoLevel) {
		if len(ctx)%2 != 0 {
			root.Error(errCtx)
			return
		}
		root.WithFields(getFields(ctx...)).Info(msg)
	}
}

// Debug logs a message at level Debug on the standard logger.
func Debug(msg string, ctx ...interface{}) {
	if root.Logger.IsLevelEnabled(logrus.DebugLevel) {
		if len(ctx)%2 != 0 {
			root.Error(errCtx)
			return
		}
		root.WithFields(getFields(ctx...)).Debug(msg)
	}
}

// Warn logs a message at level Warn on the standard logger.
func Warn(msg string, ctx ...interface{}) {
	if root.Logger.IsLevelEnabled(logrus.WarnLevel) {
		if len(ctx)%2 != 0 {
			root.Error(errCtx)
			return
		}
		root.WithFields(getFields(ctx...)).Warn(msg)
	}
}

// Error logs a message at level Error on the standard logger.
func Error(msg string, ctx ...interface{}) {
	if root.Logger.IsLevelEnabled(logrus.ErrorLevel) {
		if len(ctx)%2 != 0 {
			root.Error(errCtx)
			return
		}
		root.WithFields(getFields(ctx...)).Error(msg)
	}
}

// Panic logs a message at level Panic on the standard logger.
func Panic(msg string, ctx ...interface{}) {
	if root.Logger.IsLevelEnabled(logrus.PanicLevel) {
		if len(ctx)%2 != 0 {
			root.Error(errCtx)
			return
		}
		root.WithFields(getFields(ctx...)).Panic(msg)
	}
}

// Fatal logs a message at level Fatal on the standard logger then the process will exit with status set to 1.
func Fatal(msg string, ctx ...interface{}) {
	if root.Logger.IsLevelEnabled(logrus.FatalLevel) {
		if len(ctx)%2 != 0 {
			root.Error(errCtx)
			return
		}
		root.WithFields(getFields(ctx...)).Fatal(msg)
	}
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
