package il.ac.bgu.cs.formalmethodsintro.base.PG;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class CircuitTest {

    FvmFacade sut = null;
    private Circuit c;

    @Before
    public void setup() {
        sut = FvmFacade.get();
        c = buildCircuit();
    }

    private Circuit buildCircuit() {
        return new Circuit() {
            @Override
            public Set<String> getInputPortNames() {
                return new HashSet<String>() {{
                    add("X");
                }};
            }

            @Override
            public Set<String> getRegisterNames() {
                return new HashSet<String>() {{
                    add("R");
                }};
            }

            @Override
            public Set<String> getOutputPortNames() {
                return new HashSet<String>() {{
                    add("Y");
                }};
            }

            @Override
            public Map<String, Boolean> updateRegisters(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
                return new HashMap<String,Boolean>() {{
                    put("R",(inputs.get("X") && !registers.get("R")) || (!inputs.get("X") && registers.get("R")));
                }};
            }

            @Override
            public Map<String, Boolean> computeOutputs(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
                return new HashMap<String,Boolean>() {{
                    put("Y",(inputs.get("X") && !registers.get("R")) || (!inputs.get("X") && registers.get("R")));
                }};
            }
        };
    }

    @Test(timeout = 2000)
    public void testTsFromCircuit() {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = sut.transitionSystemFromCircuit(c);
        Assert.assertTrue(ts.getInitialStates().size()==2);
        Assert.assertTrue(ts.getStates().size()==4);
        Assert.assertTrue(ts.getActions().size()==2);
        Assert.assertTrue(ts.getTransitions().size()==8);
        Assert.assertTrue(ts.getAtomicPropositions().size()==2); //I think it should be 3!!!
    }
}
