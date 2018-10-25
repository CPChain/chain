package apis

import (
	"net"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/commons/log"
)

// ipcListen will create a Unix socket on the given endpoint.
func ipcListen(endpoint string) (net.Listener, error) {
	// Ensure the IPC path exists and remove any previous leftover
	if err := os.MkdirAll(filepath.Dir(endpoint), 0751); err != nil {
		return nil, err
	}
	os.Remove(endpoint)
	l, err := net.Listen("unix", endpoint)
	if err != nil {
		return nil, err
	}
	os.Chmod(endpoint, 0600)
	return l, nil
}

func StartIPCEndpointWithGrpc(endpoint, proxyEndpoint, datadir string, useTls bool, apis []API) (net.Listener, *Server, error) {
	// Register all the grpc APIs exposed by the services.
	handler, err := NewServer(endpoint, datadir, useTls)
	if err != nil {
		return nil, nil, err
	}
	for _, api := range apis {
		handler.RegisterApi(api)
		log.Debug("IPC registered", "namespace", api.Namespace())
	}

	// All APIs registered, start the IPC listener.
	listener, err := ipcListen(endpoint)
	if err != nil {
		return nil, nil, err
	}

	handler.Serve(proxyEndpoint, listener)
	return listener, handler, nil
}

func StartHTTPEndpoint(endpoint, proxyEndpoint, datadir string, useTls bool, apis []API, modules []string) (net.Listener, *Server, error) {
	whitelist := make(map[string]bool)
	for _, module := range modules {
		whitelist[module] = true
	}

	handler, err := NewServer(endpoint, datadir, useTls)
	if err != nil {
		return nil, nil, err
	}
	for _, api := range apis {
		if whitelist[api.Namespace()] || (len(whitelist) == 0 && api.IsPublic()) {
			handler.RegisterApi(api)
			log.Debug("HTTP registered", "namespace", api.Namespace())
		}
	}

	// All APIs registered, start the HTTP listener
	listener, err := net.Listen("tcp", endpoint)
	if err != nil {
		return nil, nil, err
	}

	handler.Serve(proxyEndpoint, listener)
	return listener, handler, nil
}
