# Chisel 

**Chisel** is a proof obligation generator for [**HABS**](http://arxiv.org/abs/1906.05704), which 
translates distributed Cyber-Physical Systems modeled as Hybrid Active Objects into Differential Dynamic Logic formulas that are passed to [**KeYmaera X**](https://github.com/LS-Lab) 4.8 

**Chisel** is at an early development stage and does not handle any data type but Real. 
Chisel will be merged with [**Crowbar**](https://github.com/Edkamb/crowbar-tool) once it leaves the experimental stage to cover full HABS.

## Specification
**Chisel** assumes that the following declarations are present in the input model:

```
data HybridSpec =  ObjInv(String) | Ensures(String) | Requires(String) | Tactic(String);
type Real = Rat;
```

All specifications are dL formulas as Strings.
The following specifications are supported:
- Object invariants are specified by an `ObjInv` annotation at the `physical` block.
- Creation conditions are specified by an `Requires` annotation at the `class` declaration.
```
[HybridSpec: Requires("x >= 0")]
class C(Real inX){
[HybridSpec: ObjInv("x >= 0")]
physical{ Real x = inX : x' = 1; }
}
```
- Method pre and post-conditions are specified by `Ensures` and `Requires` annotations in the interface.
- If a special tactic has to be applied by KeYmaera X for a certain proof, it can be annotated using `Tactic`.
The tactic for the initial block has to be annotated at the `class` declaration. Input tactic for `--zeno` are not supported.  


## Examples
The directory examples/Demo contains some examples.
To verify them download the KeYmaera X jar file *execute it once to populate the lemma database* and build an executable jar file of Chisel with  ` ./gradlew shadowJar `.
C
For general information, run `java -jar build/libs/Chisel-0.2-all.jar --help `.

To prove that the time controlled water tank example is free of locally Zeno behavior, run

```   
java -jar ./build/libs/Chisel-0.2-all.jar --kyx <path/to/keymaerax.jar> --zeno=Demo.TTank Demo/Tank.abs
```
 
To prove safety of the self-controlled limited growth element, run

```   
java -jar ./build/libs/Chisel-0.2-all.jar --kyx <path/to/keymaerax.jar> --full Demo/Growth.abs
```   


To prove safety of the locally controlled water tank, run

```   
java -jar ./build/libs/Chisel-0.2-all.jar --kyx <path/to/keymaerax.jar> --uniform --class=Demo.LTank Demo/Tank.abs
```   
 
To prove safety of the remaining two water tanks (local and timed control) using controllers, run

```
java -jar ./build/libs/Chisel-0.2-all.jar --kyx <path/to/keymaerax.jar> --control --class=Demo.CTank Demo/Tank.abs
java -jar ./build/libs/Chisel-0.2-all.jar --kyx <path/to/keymaerax.jar> --control --class=Demo.TTank Demo/Tank.abs
```
  
