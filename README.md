# Chisel 

**Chisel** is a proof obligation generator for [**HABS**](http://arxiv.org/abs/1906.05704), which 
translates distributed Cyber-Physical Systems modeled as Hybrid Active Objects into Differential Dynamic Logic formulas that are passed to [**KeYmaera**](https://github.com/LS-Lab) X 4.8 

**Chisel** is at a very early development stage and does not handle any data type but Real. Chisel will be merged with [**Crowbar**](https://github.com/Edkamb/crowbar-tool) once it leaves the experimental stage to cover full HABS.

## Examples
> ./gradlew shadowJar
> java -jar build/libs/Chisel-0.1-all.jar --kyx=<path/to/keymaerax.jar>  --full --control examples/TankMono.abs
> java -jar build/libs/Chisel-0.1-all.jar --kyx=<path/to/keymaerax.jar>  --zeno NTank.CNonZenoTank examples/TankMono.abs
