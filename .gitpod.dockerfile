FROM gitpod/workspace-full

# 0. Switch to root
USER root

# 1. Install direnv & git-lfs
RUN sudo apt-get install -y \ 
                    direnv \
                    git-lfs

# 2. Configure Nix
CMD /bin/bash -l
USER gitpod
ENV USER gitpod
WORKDIR /home/gitpod

RUN mkdir -p /home/gitpod/.config/nixpkgs && echo '{ allowUnfree = true; }' >> /home/gitpod/.config/nixpkgs/config.nix

RUN echo '. /home/gitpod/.nix-profile/etc/profile.d/nix.sh' >> /home/gitpod/.bashrc
RUN echo 'eval "$(direnv hook bash)"' >> /home/gitpod/.bashrc

# n. Give back control
USER root