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

package private

const (
	DefaultIpfsUrl = "3.0.198.89:5001"
	Dummy          = "dummy"
	IPFS           = "ipfs"
	Swarm          = "swarm"

	// disable private transaction function by default
	SupportPrivateTxFlag = true
)

type Config struct {
	RemoteDBParams string
	RemoteDBType   string
}

func DefaultConfig() Config {
	return Config{
		RemoteDBType:   Dummy,
		RemoteDBParams: DefaultIpfsUrl,
	}
}
