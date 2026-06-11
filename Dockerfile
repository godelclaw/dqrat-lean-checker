FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends \
    bash \
    build-essential \
    ca-certificates \
    curl \
    git \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/root/.elan
ENV PATH=/root/.elan/bin:$PATH

WORKDIR /opt/dqrat-lean-checker

COPY lean-toolchain ./lean-toolchain

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --default-toolchain none

RUN elan toolchain install "$(cat lean-toolchain)" \
    && elan default "$(cat lean-toolchain)"

COPY . .

RUN chmod +x scripts/verify_everything.sh scripts/run_parser_regressions.sh scripts/crosscheck_cpp.sh

CMD ["./scripts/verify_everything.sh"]
