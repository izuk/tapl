with import <nixpkgs> { };

let agda1 = agda.withPackages [ agdaPackages.standard-library ];

in mkShell {
  buildInputs = [ agda1 ];
}
