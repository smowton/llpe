---
layout: page
title: Command-line Argument or Environment Specialisation
permalink: /argvspec/
---

This example will teach how to generate a version of a program that is unconditionally specialised with respect to particular command-line arguments.

Here is our input program:

```
unsigned long strlen(const char* s) {

  unsigned long ret = 0;
  while(s[ret])
    ++ret;
  return ret;

}

int main(int argc, char** argv) {

  if(argc < 2)
    return -1;
  else
    return strlen(argv[1]);

}
```

We define our own version of <tt>strlen</tt> so we don't need to bitcode-compile the C library.

Now suppose we'd like to specialise it with respect to a particular invocation - for example, maybe a certain script always uses it in the context <tt>/usr/bin/strlen_test "Hello world!"</tt>

We need to write a file containing the arguments desired. Make a file <tt>/tmp/argv</tt> containing:

```
/usr/bin/strlen_test
Hello world!
```

Now we can create the specialisation (using the same definition of <tt>$LLPE_OPT</tt> as in the [tutorial](/tutorial/)). Supposing the input program is called strlen_test.c:

```
clang -emit-llvm -c strlen_test.c -o strlen_test.bc
$LLPE_OPT -spec-argv 0,1,/tmp/argv \
	  strlen_test.bc \
	  -o strlen_test_spec.bc
```

The <tt>0,1</tt> in 'spec-argv' says which arguments of the specialisation root (here the default, <tt>main</tt>) should be set to define the command-line arguments. <tt>0,1</tt> specifies the standard <tt>main(int argc, char** argv)</tt> arguments, but you might need to adjust these if your entry point looks different, so e.g. <tt>mymain(int mode, int argc, char** argv)</tt> would require <tt>-llpe-root mymain -spec-argv 1,2,/tmp/argv</tt>.

The LLPE GUI will appear and show the results of specialisation. Choose File -> Exit to accept the results and write the specialised bitcode.

Finally we can test the specialised program looks and sounds as we'd hope. Running <tt>llvm-dis strlen_test_spec.bc reveals:

```
define i32 @main(i32 %argc, i8** noalias %argv) #0 {
  store i8* getelementptr inbounds ([23 x i8], [23 x i8]* @spec_env_str, i64 0, i64 0), i8** %argv
  %1 = getelementptr i8*, i8** %argv, i64 1
  store i8* getelementptr inbounds ([23 x i8], [23 x i8]* @spec_env_str, i64 0, i64 10), i8** %1
  %2 = getelementptr i8*, i8** %argv, i64 2
  store i8* null, i8** %2
  %3 = call i8* @llvm.stacksave()
  call void @llvm.stackrestore(i8* %3)
  ret i32 12
}
```

The stores to <tt>argv</tt> ensure that the args are as expected (though in truth they are not needed, and a run through <tt>opt</tt> would remove them). Note there is no check that the user actually provided the argument "Hello world!" -- that would be conditional specialisation, which is documented [elsewhere](/conditionalspec/). As we'd expect the program now always returns '12', the length of "Hello world!".

Along similar lines we can specialise with respect to the environment. Usually we would read it using libc functions like <tt>getenv</tt>, but again to avoid having to build a whole libc as bitcode for our example we'll write our own. LLPE's current implementation supplies an argument to the specialisation root function, as it was developed for use with a libc entry point that takes <tt>environ</tt> as an argument, so a suitable input program might be:

```
extern char** environ;

unsigned long mystrlen(const char* s) {

  unsigned long ret = 0;
    while(s[ret])
       ++ret;
  return ret;

}

int mystrncmp(const char* s1, const char* s2, int lim) {

  int i;
  for(i = 0; s1[i] && s2[i] && i < lim; ++i) {
    int diff = s1[i] - s2[i];
    if(diff != 0)
      return diff;
  }

  if(i == lim)
    return 0;

  if(s1[i])
    return 1;
  else if(s2[i])
    return -1;
  return 0;

}

char* mygetenv(const char* key, char** env) {

  int i;
  int keylen = mystrlen(key);

  for(i = 0; env[i] != 0; ++i) {
    if(mystrncmp(env[i], key, keylen) == 0)
      return env[i] + keylen + 1;
  }

  return 0;

}

int env_spec_root(int argc, char** argv, char** env) {

  return !!mygetenv("MYKEY", env);

}

int main(int argc, char** argv) {

  return env_spec_root(argc, argv, environ);

}
```

Similar to the argv example above, we supply a file giving the environment we want, such as <tt>/tmp/env</tt>:

```
MYKEY=myval
```

We should specialise starting at <tt>env_spec_root</tt>, like this:

```
clang -emit-llvm -c env_test.c -o env_test.bc
$LLPE_OPT -spec-env 2,/tmp/env \
	  -llpe-root env_spec_root \
	  env_test.bc \
	  -o env_test_spec.bc
```

Again accepting the default specialisation decisions shown by the GUI, we'll end up with a specialised function like:

```
define i32 @env_spec_root(i32 %argc, i8** %argv, i8** %env) #0 {
  %1 = call i8* @llvm.stacksave()
  %2 = call i8* @llvm.stacksave()
  call void @llvm.stackrestore(i8* %2)
  %3 = call i8* @llvm.stacksave()
  call void @llvm.stackrestore(i8* %3)
  call void @llvm.stackrestore(i8* %1)
  ret i32 1
}
	      
```

Aside from the stack-manipulation noise which should optimise away, it simply returns '1' according to the assumption given that 'MYKEY' is defined.

These two examples have some obvious weaknesses-- they are only applicable when the <tt>argv</tt> and <tt>environ</tt> contents can be given precisely (so e.g. we can't easily accommodate a specialisation with respect to, say <tt>-a</tt> appearing somewhere in an otherwise unknown argument list), and the specialisations are unconditional (there is no runtime check that the environment or arguments match the assertion we made during specialisation). Such simple specialisation might be useful when we have total control over how the specialised binary is used, so we can be sure the arguments are as expected -- however if this is not the case, you should use [path conditions](/conditionalspec/) to make less blunt assertions with optional runtime checking. For example, if our target program used <tt>getopt</tt> and friends to populate a global structure:

```
struct global_args {

  char* input_file;
  char* output_file;
  int a_flag_given;
  int b_flag_given;
  
};
```

Then we could use path conditions to assert that, when the getopt loop completes, <tt>a_flag_given</tt> is '1' and <tt>input_file</tt> is <tt>/etc/group</tt>, but leave <tt>output_file</tt> and <tt>b_flag_given</tt> undefined.