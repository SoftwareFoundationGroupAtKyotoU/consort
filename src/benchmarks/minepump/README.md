To invoke a minepump example, use the `mwrap` included in this directory. The general use is 

```
./mwrap [test-script] [options] ./variants/.../minepump.imp
```

The test script is any script which takes `[options]` and expects an imp file as an argument.
The mrwap script will compile the minepump variant including the implementations actions, environments, etc.
