package edu.kyoto.fos.regnant;

import fj.P;
import fj.P2;
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.yaml.snakeyaml.Yaml;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;
import java.util.jar.JarFile;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class GenerateWork {
  public static void main(String[] args) throws IOException {
    if(args.length != 2) {
      System.out.println("quit");
      return;
    }
    JarFile jf = new JarFile(args[0]);
    Map<String, Boolean> work = jf.stream().filter(je -> je.getName().endsWith(".class")).flatMap(je -> {
      try(InputStream is = jf.getInputStream(je)) {
        ClassReader cr = new ClassReader(is);
        var b = new boolean[] { false, false };
        cr.accept(new ClassVisitor(Opcodes.ASM5) {
          @Override public MethodVisitor visitMethod(final int access, final String name, final String desc, final String signature, final String[] exceptions) {
            if((access & Opcodes.ACC_STATIC) == 0 || !name.equals("main") || !desc.equals("([Ljava/lang/String;)V")) {
              return null;
            }
            b[0] = true;
            return new MethodVisitor(Opcodes.ASM5) {
              @Override public AnnotationVisitor visitAnnotation(final String desc, final boolean visible) {
                if(desc.equals("Lannotation/ExpectFail;")) {
                  b[1] = true;
                }
                return null;
              }
            };
          }
        }, ClassReader.SKIP_CODE);
        if(b[0]) {
          return Stream.of(P.p(cr.getClassName(), b[1]));
        } else {
          return Stream.empty();
        }
      } catch (IOException e) {
        return Stream.empty();
      }
    }).collect(Collectors.toMap(P2::_1, P2::_2));
    try(FileWriter fw = new FileWriter(new File(args[1]))) {
      Yaml y = new Yaml();
      y.dump(work, fw);
    }
  }
}
