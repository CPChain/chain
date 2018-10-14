package log

import (
	"io"

	"github.com/Sirupsen/logrus"
)

const errCtx = "Normalized odd number of arguments by adding nil"

const (
	PanicLevel = logrus.PanicLevel
	FatalLevel = logrus.FatalLevel
	ErrorLevel = logrus.ErrorLevel
	WarnLevel  = logrus.WarnLevel
	InfoLevel  = logrus.InfoLevel
	DebugLevel = logrus.DebugLevel
)

type (
	Level         = logrus.Level
	Formatter     = logrus.Formatter
	TextFormatter = logrus.TextFormatter
	JSONFormatter = logrus.JSONFormatter
)

type Logger struct {
	*logrus.Entry
}

func New(ctx ...interface{}) *Logger {
	if len(ctx)%2 != 0 {
		logrus.Error(errCtx)
		return nil
	}

	l := &Logger{
		logrus.WithFields(getFields(ctx)),
	}

	l.SetFormatter(&TextFormatter{
		ForceColors:      true,
		QuoteEmptyFields: true,
		TimestampFormat:  termTimeFormat,
	})

	return l
}

// SetLevel sets the logger level.
func (logger *Logger) SetLevel(level logrus.Level) {
	logger.Logger.SetLevel(level)
}

// GetLevel returns the logger level.
func (logger *Logger) GetLevel() logrus.Level {
	return logger.Logger.GetLevel()
}

// SetOutput sets the logger output.
func (logger *Logger) SetOutput(output io.Writer) {
	logger.Logger.SetOutput(output)
}

// SetFormatter sets the logger formatter.
func (logger *Logger) SetFormatter(formatter Formatter) {
	logger.Logger.SetFormatter(formatter)
}

// Info logs a message at level Info on the standard logger.
func (logger *Logger) Info(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.InfoLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Info(logrus.InfoLevel, msg)
	}
}

// Debu logs a message at level Debug on the standard logger.
func (logger *Logger) Debug(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.DebugLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Debug(logrus.DebugLevel, msg)
	}
}

// Print logs a message at level Info on the standard logger.
func (logger *Logger) Print(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.InfoLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Info(logrus.InfoLevel, msg)
	}
}

// Warn logs a message at level Info on the standard logger.
func (logger *Logger) Warn(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.WarnLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Warn(logrus.WarnLevel, msg)
	}
}

// Error logs a message at level Info on the standard logger.
func (logger *Logger) Error(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.ErrorLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Error(logrus.ErrorLevel, msg)
	}
}

// Panic logs a message at level Info on the standard logger.
func (logger *Logger) Panic(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.PanicLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Panic(logrus.PanicLevel, msg)
	}
}

// Fatal logs a message at level Info on the standard logger.
func (logger *Logger) Fatal(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.FatalLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Fatal(logrus.FatalLevel, msg)
	}
}
