# The explainer, on its own port.
#
#   docker buildx build --builder multiarch --platform linux/amd64,linux/arm64 \
#     -t durwasa/tatami-explainer:latest --push explainer
#   docker run --rm -p 8430:8430 durwasa/tatami-explainer
#
# A separate image from durwasa/tatami rather than a third server in it: the
# explainer is a static site, so it needs neither the generator nor the stores,
# and rebuilding it should not mean rebuilding Lean and OCaml.
#
# The build context is this directory alone. Nothing here runs `npm run
# extract` -- src/data/*.json are generated from the repository and checked in,
# so the image serves exactly what was committed.

# ---- the build --------------------------------------------------------------
FROM node:20-alpine AS build
WORKDIR /src

# Lockfile first, so editing a component does not reinstall node_modules.
COPY package.json package-lock.json ./
RUN npm ci --no-audit --no-fund

COPY index.html vite.config.js ./
COPY src src
RUN npm run build

# ---- what runs --------------------------------------------------------------
# The unprivileged nginx image, so the server does not run as root. It cannot
# bind below 1024, which suits a fixed port of 8430.
FROM nginxinc/nginx-unprivileged:1.27-alpine

COPY nginx.conf /etc/nginx/conf.d/default.conf
COPY --from=build /src/dist /usr/share/nginx/html

EXPOSE 8430

HEALTHCHECK --interval=30s --timeout=4s --start-period=5s --retries=3 \
  CMD wget -q -O /dev/null http://127.0.0.1:8430/ || exit 1
