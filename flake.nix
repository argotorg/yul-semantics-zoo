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
        packages = [ pkgs.elan pkgs.solc pkgs.go-ethereum serve-docs ];
      };
    });
  };
}
