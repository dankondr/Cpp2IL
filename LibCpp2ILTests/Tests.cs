using System;
using System.Threading.Tasks;
using System.Net.Http;
using AssetRipper.Primitives;
using LibCpp2IL;
using Xunit;

namespace LibCpp2ILTests;

public class Tests
{
    private readonly ITestOutputHelper _outputHelper;

    public Tests(ITestOutputHelper outputHelper)
    {
        _outputHelper = outputHelper;

        //Configure the lib.
        LibCpp2IlMain.Settings.DisableGlobalResolving = true;
        LibCpp2IlMain.Settings.DisableMethodPointerMapping = true;
        LibCpp2IlMain.Settings.AllowManualMetadataAndCodeRegInput = false;
    }

    private static HttpClient client = new() { Timeout = TimeSpan.FromMinutes(5) };

    private async Task CheckFiles(string metadataUrl, string binaryUrl, UnityVersion unityVer)
    {
        _outputHelper.WriteLine($"Downloading: {metadataUrl}...");
        var metadataBytes = await client.GetByteArrayAsync(metadataUrl);
        _outputHelper.WriteLine($"Got {metadataBytes.Length / 1024 / 1024} MB metadata file.");

        _outputHelper.WriteLine($"Downloading: {binaryUrl}...");
        var binaryBytes = await client.GetByteArrayAsync(binaryUrl);
        _outputHelper.WriteLine($"Got {binaryBytes.Length / 1024 / 1024} MB binary file.");

        _outputHelper.WriteLine("Invoking LibCpp2IL...");
        var context = LibCpp2IlContextBuilder.Build(binaryBytes, metadataBytes, unityVer);
        Assert.NotNull(context);
        Assert.NotNull(context.Binary);
        Assert.NotNull(context.Metadata);
        _outputHelper.WriteLine("Done.");
    }

    [Fact]
    public async Task Metadata24_1_64BitSupportIsPresent() => await CheckFiles("http://samboycoding.me/static/meta_24.1_x64.dat", "http://samboycoding.me/static/GA_24.1_x64.dll", new UnityVersion(2018, 4, 20));

    [Fact]
    public async Task Metadata24_3_32BitSupportIsPresent() => await CheckFiles("http://samboycoding.me/static/meta_24.3_x64.dat", "http://samboycoding.me/static/GA_24.3_x64.dll", new UnityVersion(2019, 4, 11));

    [Fact]
    public async Task Metadata24_3_ARM32ElfSupportIsPresent() => await CheckFiles("http://samboycoding.me/static/meta_24.3_arm32.dat", "http://samboycoding.me/static/GA_24.3_arm32.so", new UnityVersion(2019, 4, 20));

    [Fact]
    public async Task Metadata27_1_32BitSupportIsPresent() => await CheckFiles("http://samboycoding.me/static/meta_27.1_x32.dat", "http://samboycoding.me/static/GA_27.1_x32.dll", new UnityVersion(2020, 2, 6));

    [Fact]
    public async Task Metadata27_1_AARCH64ElfSupportIsPresent() => await CheckFiles("http://samboycoding.me/static/meta_27.1_aarch64.dat", "http://samboycoding.me/static/GA_27.1_aarch64.so", new UnityVersion(2020, 2, 6));
}
