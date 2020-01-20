package il.ac.bgu.cs.formalmethodsintro.base.examples;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import static java.util.Arrays.asList;

import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;

public class SemaphoreBasedMutualExclusionBuilder {

    public static ProgramGraph<String, String> build(int id) {
        ProgramGraph<String, String> pg = new ProgramGraph<>();

        String noncrit = "noncrit" + id;
        String wait = "wait" + id;
        String crit = "crit" + id;

        pg.addLocation(noncrit);
        pg.addLocation(wait);
        pg.addLocation(crit);

        pg.setInitial(noncrit, true);

        pg.addTransition(new PGTransition<>(noncrit, "true", "", wait));
        pg.addTransition(new PGTransition<>(wait, "y>0", "y:=y-1", crit));
        pg.addTransition(new PGTransition<>(crit, "true", "y:=y+1", noncrit));

        pg.addInitalization(asList("y:=1"));

        return pg;

    }

}
