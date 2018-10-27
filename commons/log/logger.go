package log

import (
	"io"
	"sync"

	"github.com/Sirupsen/logrus"
	filename "github.com/keepeye/logrus-filename"
)

const errCtx = "Normalized odd number of arguments by adding nil"

const (
	PanicLevel          = logrus.PanicLevel
	FatalLevel          = logrus.FatalLevel
	ErrorLevel          = logrus.ErrorLevel
	WarnLevel           = logrus.WarnLevel
	InfoLevel           = logrus.InfoLevel
	DebugLevel          = logrus.DebugLevel
	DefaultFilenameHook = 3
)

type (
	Level         = logrus.Level
	Formatter     = logrus.Formatter
	TextFormatter = logrus.TextFormatter
	JSONFormatter = logrus.JSONFormatter
)

type Logger struct {
	*logrus.Entry
	needSkip     bool
	once         *sync.Once
	filenameHook *filename.Hook
}

func New(ctx ...interface{}) *Logger {
	var l *Logger
	opt := len(ctx)
	switch {
	case opt == 0:
		l = &Logger{
			Entry: logrus.NewEntry(logrus.New()),
			once:  new(sync.Once),
		}
	case (opt % 2) == 0:
		l = &Logger{
			Entry: logrus.WithFields(getFields(ctx)),
			once:  new(sync.Once),
		}
	default:
		logrus.Error("argument number wrong")
		return nil
	}

	l.SetFormatter(&TextFormatter{
		FullTimestamp:    true,
		QuoteEmptyFields: true,
		TimestampFormat:  termTimeFormat,
	})

	return l
}

func (logger *Logger) skip() {
	logger.needSkip = true
}

// ShowFilename show filename and position
func (logger *Logger) ShowFilename() {
	logger.once.Do(func() {
		logger.filenameHook = filename.NewHook()
		if logger.needSkip {
			logger.filenameHook.Skip += 1
		}
		logger.filenameHook.Skip += DefaultFilenameHook
		logger.filenameHook.Field = "Line"
		// logger.Entry.Logger.Hooks
		logger.Entry.Logger.AddHook(logger.filenameHook)
	})
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
		logger.WithFields(getFields(args...)).Info(msg)
	}
}

// Debu logs a message at level Debug on the standard logger.
func (logger *Logger) Debug(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.DebugLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Debug(msg)
	}
}

// Print logs a message at level Info on the standard logger.
func (logger *Logger) Print(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.InfoLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Info(msg)
	}
}

// Warn logs a message at level Info on the standard logger.
func (logger *Logger) Warn(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.WarnLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Warn(msg)
	}
}

// Error logs a message at level Info on the standard logger.
func (logger *Logger) Error(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.ErrorLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Error(msg)
	}
}

// Panic logs a message at level Info on the standard logger.
func (logger *Logger) Panic(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.PanicLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Panic(msg)
	}
}

// Fatal logs a message at level Info on the standard logger.
func (logger *Logger) Fatal(msg string, args ...interface{}) {
	if logger.Logger.IsLevelEnabled(logrus.FatalLevel) {
		if len(args)%2 != 0 {
			root.Error(errCtx)
			return
		}
		logger.WithFields(getFields(args...)).Fatal(msg)
	}
}
