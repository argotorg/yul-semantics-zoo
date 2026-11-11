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
    devShells = forAllSystems (pkgs: let
      # solc 0.8.38, the version of the docs: nixpkgs has an older one. The release binaries are
      # static on linux and universal on mac.
      solc = let
        asset = {
          x86_64-linux = { name = "solc-static-linux"; hash = "sha256-ZcMYCjNuq7a9xLvUnMQFrrIzl2lkrmwR+6KmyL6PMkM="; };
          aarch64-linux = { name = "solc-static-linux-arm"; hash = "sha256-ephsj4WUX+x4DSy7NSzdhZWbciLdM4MKdWPCr0vB/KA="; };
          aarch64-darwin = { name = "solc-macos"; hash = "sha256-sYrB0fSDlMccqa778PuU/vJMh7NY9IV43llB4jTgoqk="; };
        }.${pkgs.stdenv.hostPlatform.system};
        bin = pkgs.fetchurl {
          url = "https://github.com/argotorg/solidity/releases/download/v0.8.38/${asset.name}";
          inherit (asset) hash;
        };
      in pkgs.runCommand "solc-0.8.38" { } ''
        install -Dm755 ${bin} $out/bin/solc
      '';
      # `serve-docs [port]`: build the literate site, serve it (port 8000 if not given), rebuild
      # it when a source changes, and reload the browser when it is rebuilt
      serve-docs = pkgs.writeShellApplication {
        name = "serve-docs";
        runtimeInputs = [ pkgs.watchexec pkgs.python3Packages.livereload ];
        text = ''
          port="''${1:-8000}"
          if [ ! -f literate.toml ]; then
            echo "serve-docs: run it in the root of the repository" >&2
            exit 1
          fi
          site="$(lake query :literateHtml)"
          watchexec --postpone -w YulSemnaticsZoo -w YulSemnaticsZoo.lean -w literate.toml -w doc \
            -- lake query :literateHtml &
          watcher=$!
          trap 'kill "$watcher"' EXIT
          livereload -p "$port" -w 1 "$site"
        '';
      };
    in {
      default = pkgs.mkShell {
        packages = [ pkgs.elan solc pkgs.go-ethereum serve-docs ];
      };
    });
  };
}
