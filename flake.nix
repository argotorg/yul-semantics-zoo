{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixpkgs-unstable/nixexprs.tar.zst";
  };

  outputs = inputs: let
    systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
    forAllSystems = f: inputs.nixpkgs.lib.genAttrs systems
      (system: f inputs.nixpkgs.legacyPackages.${system});
  in {
    devShells = forAllSystems (pkgs: {
      default = pkgs.mkShell {
        packages = [ pkgs.elan ];
      };
    });
  };
}
