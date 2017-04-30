# SimplPublic

## Simpl : Synthesizer for imperative language
Simpl is a program synthesizer which aims to synthesize imperative programs from examples.
Simpl is the first synthesizer that adopts semantic-based static analysis 
to efficiently generate the programs. This is co-work with 
Prof.Hakjoo Oh in Korea University (http://prl.korea.ac.kr). 

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
For more informations, please refer to the following link:
https://arxiv.org/abs/1702.06334

## Question
If you have any questions, please email to: 
sunbeom\_so@korea.ac.kr. 
