# verify-systemic-properties Docker Container

This repository contains the Dockerfile and instructions for the **verify-systemic-properties** Docker container, which provides a pre-configured environment for the formal verification of invariants in control systems using **Frama-C** and **Alt-Ergo-Poly**.

## Pulling and Running the Docker Image

To pull the Docker image from Docker Hub and run it, follow these steps:

1. **Install Docker on your machine**  
   If you haven't installed Docker yet, follow the official installation guide for your operating system here: [Get Docker](https://docs.docker.com/get-docker/).

2. **Open a terminal or command prompt** on your machine.

3. **Pull the verify-systemic-properties image from Docker Hub:**

    ```bash
    docker pull tacas2025/verify-systemic-properties:latest
    ```

    This command will download the **verify-systemic-properties** Docker image to your local machine.

4. **Run a container using the pulled image:**

    ```bash
    docker run -it tacas2025/verify-systemic-properties:latest /bin/bash
    ```

    This command starts a new container using the pulled Docker image and provides an interactive terminal session.

## Running Commands in the Container

Once inside the container, you need to run the following commands before executing any other commands:

1. **Initialize the OPAM environment:**

    ```bash
    eval $(opam env)
    ```

    This command sets the required environment variables for the OPAM package manager, allowing you to properly use the installed tools, including **Frama-C**, **Why3**, and **Alt-Ergo-Poly**.

2. **Run the Makefile:**

    ```bash
    make
    ```

    The Makefile contains the necessary instructions to compile and run the formal verification process on the provided C files. Running `make` will execute the verification process using the pre-configured tools and settings.
