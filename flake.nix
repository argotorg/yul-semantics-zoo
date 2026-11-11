{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixpkgs-unstable/nixexprs.tar.zst";
  };

  outputs = inputs: let
    # x86_64-darwin is not supported by nixpkgs since 26.11
    systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
    forAllSystems = f: inputs.nixpkgs.lib.genAttrs systems
      (system: f inputs.nixpkgs.legacyPackages.${system});
  in {
    packages = forAllSystems (pkgs: {
      hello = pkgs.hello;

      default = inputs.self.packages.${pkgs.stdenv.hostPlatform.system}.hello;
    });

    devShells = forAllSystems (pkgs: {
      default = pkgs.mkShell {
        packages = [ pkgs.elan ];
      };
    });
  };
}
