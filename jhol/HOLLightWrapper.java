package edu.siu.math.egut.jhol;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Static algorithms that don't fit (logically) in any other class.
 * @author Joe Pleso
 *
 */
final class HOLLightWrapper {

    /**
     * 
     */
    public static final char LIE_UNDERSCORE = '_';
    /**
     * 
     */
    public static final char LIE_PLUS = '+';
    /**
     * 
     */
    public static final char LIE_X = 'X';
    /**
     * 
     */
    public static final char LIE_MINUS = '-';
    /**
     * 
     */
    public static final char LIE_LEFT_PARENTHESIS = '(';
    /**
     * 
     */
    public static final char LIE_RIGHT_PARENTHESIS = ')';
    /**
     * 
     */
    public static final char LIE_COMMA = ',';
    /**
     * 
     */
    public static final char LIE_LEFT_SQUARE_BRACKET = '[';
    /**
     * 
     */
    public static final char LIE_RIGHT_SQUARE_BRACKET = ']';
    /**
     * 
     */
    public static final char LIE_SPACE = ' ';
    /**
     * 
     */
    public static final char LIE_NEWLINE = '\n';
    /**
     * 
     */
    public static final char LIE_QUOTE = '\"';
    /**
     * 
     */
    public static final char LIE_BACKSLASH = '\\';
    /**
     * 
     */
    public static final String LIE_PRINT_COMMAND = "print";
    /**
     * 
     */
    public static final char LIE_PROMPT_1 = '>';
    /**
     * 
     */
    public static final char LIE_PROMPT_2 = '\\';
    /**
     * 
     */
    public static final String LIE_PARTING_MESSAGE = "end program";
    /**
     * 
     */
    public static final char LIE_COMMENT = '#';
    /**
     * 
     */
    public static final String LIE_DEFAULT_GROUP_FUNCTION =
            "default";
    /**
     * 
     */
    public static final String LIE_DEFAULT_GROUP_FUNCTION_DEFINITION =
            LIE_DEFAULT_GROUP_FUNCTION + "(grp g)=g";
    /**
     * 
     */
    public static final char LIE_N = 'N';

    static List<String> preParse(String g) {
        String[] goals;

        goals = g.split("\n");

        List<String> result = new ArrayList<String>();
        for (int i = 0; i < goals.length; i ++){
            if (goals[i].length() > 0 && goals[i].charAt(0) == '`'){
                String s = goals[i].substring(1, goals[i].length() - 1);
                String[] tmp = s.split("==>");
                StringBuilder foo = new StringBuilder();
                for (int j = 0; j < tmp.length - 1; j++){
                    foo.append(tmp[j]);
                    foo.append("⟹");
                }
                foo.append(tmp[tmp.length - 1]);
                result.add(foo.toString());
            }
                
        }


        return result;
    }

    public HOLLightWrapper() {
        ocampl = this.getNewProcess();
        Process proc = ocampl;
        in = proc.getInputStream();
        out = proc.getOutputStream();

        bin = new BufferedWriter(
                new OutputStreamWriter(out));
        bout = new BufferedReader(
                new InputStreamReader(in));
        berr = new BufferedReader(
                new InputStreamReader(proc.getErrorStream()));


    }
    private final InputStream in;
    private final OutputStream out;
    private final BufferedWriter bin;
    private final BufferedReader bout;
    private final BufferedReader berr;

    @Override
    protected void finalize() throws Throwable {
        super.finalize();
        in.close();
        out.close();
        bin.close();
        bout.close();
        berr.close();

    }
    public boolean REDIRECT = false;
    private boolean redirect = REDIRECT;
    private final Process ocampl;

    private Process getNewProcess() {

        ProcessBuilder proc = new ProcessBuilder(
                "/usr/local/bin/hol_light");
        proc.redirectErrorStream(redirect);
        try {
            return proc.start();
        } catch (IOException e) {
            return null;
        }

    }



    public String flushOutput() {
        try {
            StringBuilder str = new StringBuilder();
            do {

                    char c = (char) bout.read();
                    while (c != '#') {
                        str.append(c);
                        c = (char) bout.read();
                    }
                    str.append(c);
                    str.append((char) bout.read());

            } while (bout.ready());
            return str.toString();
        } catch (IOException ex) {
            Logger.getLogger(HOLLightWrapper.class.getName()).log(Level.SEVERE, null, ex);
            return null;
        }

    }

   

    public String[] runCommand(String cmd) {


        String[] result = new String[3];
        Process proc = ocampl;


        StringBuffer str = new StringBuffer();

        if (cmd.length() == 1 ||
                cmd.charAt(cmd.length() - 1) != ';'
             || cmd.charAt(cmd.length() - 2) != ';'   )
                cmd = cmd + ";;";

        result[0] = cmd + "\n";

        try {
            bin.write(cmd);
            bin.newLine();
            bin.flush();

            str.append(flushOutput());
            result[1] = str.toString();
            str = new StringBuffer();

            if (berr.ready())
                throw new RuntimeException("Unimplemented stderr on hollight");

            /*while (berr.ready()){
            str.append(berr.readLine());

            }
            result[1] = str.toString();
             */
            return result;

        } catch (IOException e) {
            return null;
        } finally {
        }










    }
}
