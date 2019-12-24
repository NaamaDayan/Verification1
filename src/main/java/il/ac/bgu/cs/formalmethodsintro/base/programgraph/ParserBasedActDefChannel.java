package il.ac.bgu.cs.formalmethodsintro.base.programgraph;

import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.Evaluator;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaLexer;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.SpecContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.util.Util;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;

import java.util.*;

/**
 * An object that identifies and interprets the actions defined in the grammar
 * nanopromela/NanoPromela.g4
 */
public class ParserBasedActDefChannel implements ActionDef {

    //    /**
//     * @see
//     * il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef#effect(java.util.Map,
//     * java.lang.String)
//     */
    @Override
    public Map<String, Object> effect(Map<String, Object> eval, Object action) {
        if (action.equals("")) {
            return eval;
        }

        if (action.toString().contains("|"))
            return effectHandshake(eval,action);

        String channel = getChannel(action.toString());
        String var = getVar(action.toString());
        boolean isReading = action.toString().contains("?");
        Queue<String> channelQueue = ((Queue<String>)eval.get(channel));
        if (isReading && channelQueue.size()>0) {
            String queueElement = ((Queue<String>) channelQueue).poll();
            eval.replace(channel, channelQueue);
            if (!queueElement.equals("")) {
                int out = Integer.parseInt(queueElement);
                eval.replace(var, out);
            }
            return eval;
        }
        else if (!isReading) { //writing
            if (Util.isNumber(var))
                channelQueue.add(var);
            else if (var.toString().length() == 0)
                channelQueue.add("");
            else
                channelQueue.add(eval.get(var).toString());
            eval.replace(channel,channelQueue);
            return eval;
        }
        return null;
    }

    //action = c?x | c!y
    private Map<String, Object> effectHandshake(Map<String, Object> eval, Object action) {
        String[] channelActions = action.toString().split("|");
        boolean firstRead = channelActions[0].contains("?");
        if (firstRead)
            eval.replace(getVar(channelActions[0]), eval.get(getVar(channelActions[1])));
        else
            eval.replace(getVar(channelActions[1]), eval.get(getVar(channelActions[0])));
        return eval;
    }


    public static String getChannel(String action) {
        int ind = action.indexOf('?') == -1 ? action.indexOf('!') : action.indexOf('?');
        String channel = action.substring(0, ind);
        channel = channel.substring(channel.lastIndexOf(' ') + 1);
        return channel;
    }

    public static String getVar(String action) {
        int ind = action.indexOf('?') == -1 ? action.indexOf('!') : action.indexOf('?');
        String var = action.substring(ind + 1);
        int cutIndex = var.indexOf(' ') != -1 ? var.indexOf(' ') : var.length();
        var = var.substring(0, cutIndex);
        return var;
    }

    /**
     * Parse the action.
     *
     * @param action A string that represents an action
     * @return The root of the parse tree or null, if the string cannot be
     * parsed.
     */
    private StmtContext parseAction(String action) {
        NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(action));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        NanoPromelaParser parser = new NanoPromelaParser(tokens);

        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowingErrorListener());

        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowingErrorListener());

        try {
            SpecContext spec = parser.spec();
            StmtContext p = spec.stmt();
            return p;
        } catch (RecognitionException ex) {
            return null;
        }
    }

    //    /**
//     * @see
//     * il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef#isMatchingAction(java.lang.String)
//     */
    @Override
    public boolean isMatchingAction(Object action) {
        return action.toString().contains("?") || action.toString().contains("!");
    }

}
