# SimplPublic

## Simpl : Synthesizer for imperative language
Simpl is a program synthesizer which aims to synthesize imperative programs from examples.
Simpl is the first synthesizer that adopts semantic-based static analysis 
to efficiently generate the programs. This is co-work with 
Prof.Hakjoo Oh in Korea University (http://prl.korea.ac.kr). 

## Notes
-   This work was published at SAS (Static Analysis Symposium) 2017. For details, please refer to our paper: ```Synthesizing Imperative Programs from Examples Guided by Static Analysis```
-   See the ```sas2017-snapshot``` branch for the implementation of the SAS 2017 version.
-   Further improvements (including bug fixes) will be continually updated in ```master``` branch.

## How to build
After you clone this project, type ```chmod +x build```, and then type ```./build```.
-   Clone this project.
-   Activate the build script: ```chmod +x build```.
-   Then, you can complie the whole files: ```./build```.

## How to use
To use Simpl, you need to provide:
-   A partial program with holes
-   Input-output examples
-   Resources that will be used to complete the partial program

Then, Simpl will output the complete program whose behaviour matches all the given input-output examples
by filling in the holes of the partial program.
For example, type ```./main.native -input benchmarks/no1_factorial``` to produce the complete factorial function.

## Contact
If you have any questions, please email to: 
sunbeom\_so@korea.ac.kr. 
