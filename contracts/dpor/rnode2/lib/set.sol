pragma solidity ^0.4.24;

library Set {
    /** We define a new struct datatype that will be used to
     * hold its data in the calling contract.
    */
    struct Data {
        mapping(address => bool) flags;
        address[] values;
    }

    /** Note that the first parameter is of type "storage
     * reference" and thus only its storage address and not
     * its contents is passed as part of the call.  This is a
     * special feature of library functions.  It is idiomatic
     * to call the first parameter 'self', if the function can
     * be seen as a method of that object.
    */
    function insert(Data storage self, address value)
      internal
      returns (bool)
    {
        if (self.flags[value])
            return false; // already there
        self.flags[value] = true;
        self.values.push(value);
        return true;
    }

    function remove(Data storage self, address value)
      internal
      returns (bool)
    {
        if (!self.flags[value])
            return false; // not there
        self.flags[value] = false;
        uint size = self.values.length;
        for (uint i = 0 ; i < size ; i++){
            if (self.values[i] == value){
                // cost too much gas.
                // for (uint j = i; j < size - 1; j++){
                //     self.values[j] = self.values[j+1];
                // }
                // delete self.values[size-1];
                // self.values.length--;
                // break;

                // simplify the steps to save gas.
                self.values[i] = self.values[size-1];
                delete self.values[size-1];
                self.values.length--;
                break;
            }
        }
        return true;
    }

    function contains(Data storage self, address value) internal view returns (bool) {
        return self.flags[value];
    }

    function getAll(Data storage self) internal view returns (address[]) {
        return self.values;
    }
}

