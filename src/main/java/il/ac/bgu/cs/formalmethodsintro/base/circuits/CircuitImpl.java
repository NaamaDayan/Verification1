package il.ac.bgu.cs.formalmethodsintro.base.circuits;

import java.rmi.MarshalledObject;
import java.util.*;

public class CircuitImpl implements Circuit {
    @Override
    public Set<String> getInputPortNames() {
        return new HashSet<>(Arrays.asList("x"));
    }

    @Override
    public Set<String> getRegisterNames() {
        return new HashSet<>(Arrays.asList("r1,r2"));
    }

    @Override
    public Set<String> getOutputPortNames() {
        return new HashSet<>(Arrays.asList("y"));
    }

    @Override
    public Map<String, Boolean> updateRegisters(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
        boolean reg1Output = inputs.get("x") || registers.get("r1");
        boolean reg2Output = inputs.get("x") && registers.get("r2");
        Map<String,Boolean> toRet = new HashMap<>();
        toRet.put("r1", reg1Output);
        toRet.put("r2", reg2Output);
        return toRet;
    }

    @Override
    public Map<String, Boolean> computeOutputs(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
        Map<String,Boolean> toRet = new HashMap<>();
        toRet.put("y", false);
        return toRet;
    }
}
